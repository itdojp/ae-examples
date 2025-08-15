import sodium from 'libsodium-wrappers';
import { Session } from '../entities';

export interface KeyPair {
  publicKey: Uint8Array;
  privateKey: Uint8Array;
}

export interface MessageHeader {
  dhPublicKey: string;
  previousChainLength: number;
  messageNumber: number;
}

export class DoubleRatchet {
  private DHs?: KeyPair; // DH sending key pair
  private DHr?: Uint8Array; // DH receiving public key
  private RK: Uint8Array; // Root key
  private CKs?: Uint8Array; // Sending chain key
  private CKr?: Uint8Array; // Receiving chain key
  private Ns: number = 0; // Sending message number
  private Nr: number = 0; // Receiving message number
  private PN: number = 0; // Previous chain length
  private skippedKeys: Map<string, Uint8Array> = new Map();

  constructor(rootKey: Uint8Array) {
    this.RK = rootKey;
  }

  static async initialize(): Promise<void> {
    await sodium.ready;
  }

  generateKeyPair(): KeyPair {
    const keyPair = sodium.crypto_box_keypair();
    return {
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey,
    };
  }

  async initializeAsSender(theirPublicKey: Uint8Array): Promise<void> {
    this.DHs = this.generateKeyPair();
    this.DHr = theirPublicKey;
    const sharedSecret = this.computeDH(this.DHs, this.DHr);
    const keys = await this.kdfRK(this.RK, sharedSecret);
    this.RK = keys.rootKey;
    this.CKs = keys.chainKey;
  }

  async initializeAsReceiver(): Promise<KeyPair> {
    const keyPair = this.generateKeyPair();
    this.DHs = keyPair;
    return keyPair;
  }

  async ratchetEncrypt(plaintext: Uint8Array): Promise<{ header: MessageHeader; ciphertext: Uint8Array }> {
    if (!this.CKs) {
      throw new Error('Sending chain key not initialized');
    }
    if (!this.DHs) {
      throw new Error('DH sending key pair not initialized');
    }

    const messageKey = await this.kdfCK(this.CKs);
    this.CKs = messageKey.chainKey;

    const header: MessageHeader = {
      dhPublicKey: sodium.to_base64(this.DHs.publicKey),
      previousChainLength: this.PN,
      messageNumber: this.Ns,
    };

    const nonce = sodium.randombytes_buf(sodium.crypto_secretbox_NONCEBYTES);
    const ciphertext = sodium.crypto_secretbox_easy(plaintext, nonce, messageKey.messageKey);
    
    const combined = new Uint8Array(nonce.length + ciphertext.length);
    combined.set(nonce);
    combined.set(ciphertext, nonce.length);

    this.Ns += 1;
    return { header, ciphertext: combined };
  }

  async ratchetDecrypt(header: MessageHeader, ciphertext: Uint8Array): Promise<Uint8Array> {
    const dhPublicKey = sodium.from_base64(header.dhPublicKey);
    
    const skippedKey = this.trySkippedKeys(header, ciphertext);
    if (skippedKey) {
      return skippedKey;
    }

    if (this.DHr && !this.arraysEqual(dhPublicKey, this.DHr)) {
      await this.skipMessageKeys(header.previousChainLength);
      await this.dhRatchet(dhPublicKey);
    }

    await this.skipMessageKeys(header.messageNumber);

    if (!this.CKr) {
      throw new Error('Receiving chain key not initialized');
    }

    const messageKey = await this.kdfCK(this.CKr);
    this.CKr = messageKey.chainKey;
    this.Nr += 1;

    const nonce = ciphertext.slice(0, sodium.crypto_secretbox_NONCEBYTES);
    const actualCiphertext = ciphertext.slice(sodium.crypto_secretbox_NONCEBYTES);

    const plaintext = sodium.crypto_secretbox_open_easy(actualCiphertext, nonce, messageKey.messageKey);
    if (!plaintext) {
      throw new Error('Failed to decrypt message');
    }

    return plaintext;
  }

  private async dhRatchet(dhPublicKey: Uint8Array): Promise<void> {
    this.PN = this.Ns;
    this.Ns = 0;
    this.Nr = 0;
    this.DHr = dhPublicKey;

    if (!this.DHs) {
      throw new Error('DH sending key pair not initialized');
    }

    const sharedSecret = this.computeDH(this.DHs, this.DHr);
    const keys = await this.kdfRK(this.RK, sharedSecret);
    this.RK = keys.rootKey;
    this.CKr = keys.chainKey;

    this.DHs = this.generateKeyPair();
    const sharedSecret2 = this.computeDH(this.DHs, this.DHr);
    const keys2 = await this.kdfRK(this.RK, sharedSecret2);
    this.RK = keys2.rootKey;
    this.CKs = keys2.chainKey;
  }

  private async skipMessageKeys(until: number): Promise<void> {
    if (this.Nr + 100 < until) {
      throw new Error('Too many skipped messages');
    }

    if (this.CKr) {
      while (this.Nr < until) {
        const messageKey = await this.kdfCK(this.CKr);
        this.CKr = messageKey.chainKey;
        this.storeSkippedKey(this.DHr!, this.Nr, messageKey.messageKey);
        this.Nr += 1;
      }
    }
  }

  private storeSkippedKey(dhPublicKey: Uint8Array, messageNumber: number, messageKey: Uint8Array): void {
    const key = `${sodium.to_base64(dhPublicKey)}-${messageNumber}`;
    this.skippedKeys.set(key, messageKey);
  }

  private trySkippedKeys(header: MessageHeader, ciphertext: Uint8Array): Uint8Array | null {
    const key = `${header.dhPublicKey}-${header.messageNumber}`;
    const messageKey = this.skippedKeys.get(key);
    
    if (messageKey) {
      const nonce = ciphertext.slice(0, sodium.crypto_secretbox_NONCEBYTES);
      const actualCiphertext = ciphertext.slice(sodium.crypto_secretbox_NONCEBYTES);
      
      try {
        const plaintext = sodium.crypto_secretbox_open_easy(actualCiphertext, nonce, messageKey);
        this.skippedKeys.delete(key);
        return plaintext;
      } catch {
        return null;
      }
    }
    
    return null;
  }

  private computeDH(ourKeyPair: KeyPair, theirPublicKey: Uint8Array): Uint8Array {
    return sodium.crypto_scalarmult(ourKeyPair.privateKey, theirPublicKey);
  }

  private async kdfRK(rootKey: Uint8Array, dhOutput: Uint8Array): Promise<{ rootKey: Uint8Array; chainKey: Uint8Array }> {
    const input = new Uint8Array(rootKey.length + dhOutput.length);
    input.set(rootKey);
    input.set(dhOutput, rootKey.length);
    
    const output = sodium.crypto_kdf_derive_from_key(64, 1, 'RK', rootKey.slice(0, 32));
    
    return {
      rootKey: output.slice(0, 32),
      chainKey: output.slice(32, 64),
    };
  }

  private async kdfCK(chainKey: Uint8Array): Promise<{ chainKey: Uint8Array; messageKey: Uint8Array }> {
    const messageKey = sodium.crypto_kdf_derive_from_key(32, 1, 'MK', chainKey.slice(0, 32));
    const newChainKey = sodium.crypto_kdf_derive_from_key(32, 2, 'CK', chainKey.slice(0, 32));
    
    return {
      chainKey: newChainKey,
      messageKey: messageKey,
    };
  }

  private arraysEqual(a: Uint8Array, b: Uint8Array): boolean {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }

  exportState(): any {
    return {
      DHs: this.DHs ? {
        publicKey: sodium.to_base64(this.DHs.publicKey),
        privateKey: sodium.to_base64(this.DHs.privateKey),
      } : undefined,
      DHr: this.DHr ? sodium.to_base64(this.DHr) : undefined,
      RK: sodium.to_base64(this.RK),
      CKs: this.CKs ? sodium.to_base64(this.CKs) : undefined,
      CKr: this.CKr ? sodium.to_base64(this.CKr) : undefined,
      Ns: this.Ns,
      Nr: this.Nr,
      PN: this.PN,
      skippedKeys: Array.from(this.skippedKeys.entries()).map(([k, v]) => [k, sodium.to_base64(v)]),
    };
  }

  static fromState(state: any): DoubleRatchet {
    const dr = new DoubleRatchet(sodium.from_base64(state.RK));
    
    if (state.DHs) {
      dr.DHs = {
        publicKey: sodium.from_base64(state.DHs.publicKey),
        privateKey: sodium.from_base64(state.DHs.privateKey),
      };
    }
    
    if (state.DHr) {
      dr.DHr = sodium.from_base64(state.DHr);
    }
    
    if (state.CKs) {
      dr.CKs = sodium.from_base64(state.CKs);
    }
    
    if (state.CKr) {
      dr.CKr = sodium.from_base64(state.CKr);
    }
    
    dr.Ns = state.Ns;
    dr.Nr = state.Nr;
    dr.PN = state.PN;
    
    state.skippedKeys.forEach(([k, v]: [string, string]) => {
      dr.skippedKeys.set(k, sodium.from_base64(v));
    });
    
    return dr;
  }
}