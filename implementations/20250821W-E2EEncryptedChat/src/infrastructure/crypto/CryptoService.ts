import * as sodium from 'libsodium-wrappers';
import { 
  IdentityKey, 
  SignedPreKey, 
  OneTimePreKey, 
  DeviceKey,
  CryptoKeyBundle,
  PreKeyBundle
} from '../../domain/entities/CryptoKey';

export class CryptoService {
  private static instance: CryptoService;
  private ready: boolean = false;

  private constructor() {}

  static getInstance(): CryptoService {
    if (!CryptoService.instance) {
      CryptoService.instance = new CryptoService();
    }
    return CryptoService.instance;
  }

  async init(): Promise<void> {
    if (!this.ready) {
      await sodium.ready;
      this.ready = true;
    }
  }

  async generateIdentityKeyPair(): Promise<IdentityKey> {
    await this.init();
    const keyPair = sodium.crypto_sign_keypair();
    return {
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey
    };
  }

  async generateSignedPreKey(identityKey: IdentityKey): Promise<SignedPreKey> {
    await this.init();
    const keyPair = sodium.crypto_box_keypair();
    const timestamp = new Date();
    const signature = sodium.crypto_sign_detached(
      keyPair.publicKey,
      identityKey.privateKey
    );

    return {
      id: Math.floor(Math.random() * 0xFFFFFF),
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey,
      signature,
      timestamp
    };
  }

  async generateOneTimePreKeys(count: number = 100): Promise<OneTimePreKey[]> {
    await this.init();
    const keys: OneTimePreKey[] = [];
    
    for (let i = 0; i < count; i++) {
      const keyPair = sodium.crypto_box_keypair();
      keys.push({
        id: i,
        publicKey: keyPair.publicKey,
        privateKey: keyPair.privateKey
      });
    }
    
    return keys;
  }

  async generateDeviceKey(): Promise<DeviceKey> {
    await this.init();
    const keyPair = sodium.crypto_box_keypair();
    return {
      id: sodium.to_base64(sodium.randombytes_buf(16)),
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey
    };
  }

  async generateKeyBundle(): Promise<CryptoKeyBundle> {
    await this.init();
    const identityKey = await this.generateIdentityKeyPair();
    const signedPreKey = await this.generateSignedPreKey(identityKey);
    const oneTimePreKeys = await this.generateOneTimePreKeys();
    const deviceKey = await this.generateDeviceKey();

    return {
      identityKey,
      signedPreKey,
      oneTimePreKeys,
      deviceKey
    };
  }

  async encryptMessage(
    plaintext: string,
    recipientPublicKey: Uint8Array,
    senderPrivateKey: Uint8Array
  ): Promise<{ ciphertext: Uint8Array; nonce: Uint8Array }> {
    await this.init();
    const nonce = sodium.randombytes_buf(sodium.crypto_box_NONCEBYTES);
    const message = sodium.from_string(plaintext);
    
    const ciphertext = sodium.crypto_box_easy(
      message,
      nonce,
      recipientPublicKey,
      senderPrivateKey
    );

    return { ciphertext, nonce };
  }

  async decryptMessage(
    ciphertext: Uint8Array,
    nonce: Uint8Array,
    senderPublicKey: Uint8Array,
    recipientPrivateKey: Uint8Array
  ): Promise<string> {
    await this.init();
    const decrypted = sodium.crypto_box_open_easy(
      ciphertext,
      nonce,
      senderPublicKey,
      recipientPrivateKey
    );
    
    return sodium.to_string(decrypted);
  }

  async deriveSharedSecret(
    publicKey: Uint8Array,
    privateKey: Uint8Array
  ): Promise<Uint8Array> {
    await this.init();
    return sodium.crypto_scalarmult(privateKey, publicKey);
  }

  async generateHMAC(key: Uint8Array, data: Uint8Array): Promise<Uint8Array> {
    await this.init();
    return sodium.crypto_auth(data, key);
  }

  async verifyHMAC(
    mac: Uint8Array,
    data: Uint8Array,
    key: Uint8Array
  ): Promise<boolean> {
    await this.init();
    return sodium.crypto_auth_verify(mac, data, key);
  }

  async hash(data: Uint8Array): Promise<Uint8Array> {
    await this.init();
    return sodium.crypto_generichash(32, data);
  }

  async verifySignature(
    signature: Uint8Array,
    message: Uint8Array,
    publicKey: Uint8Array
  ): Promise<boolean> {
    await this.init();
    return sodium.crypto_sign_verify_detached(signature, message, publicKey);
  }

  generateRandomBytes(length: number): Uint8Array {
    return sodium.randombytes_buf(length);
  }
}