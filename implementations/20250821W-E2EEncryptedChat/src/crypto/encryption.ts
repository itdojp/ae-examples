// E2E Encryption Service Implementation
// Based on Signal Protocol and Double Ratchet Algorithm

import {
  CipherText,
  Nonce,
  AuthenticationTag,
  EncryptedMessage,
  DoubleRatchetState,
  MessageKey,
  EphemeralKey,
  CryptoError
} from '../types';

export class EncryptionService {
  private static readonly ALGORITHM = 'AES-GCM';
  private static readonly KEY_LENGTH = 32; // 256 bits
  private static readonly TAG_LENGTH = 16; // 128 bits

  /**
   * Encrypt a message using the Double Ratchet algorithm
   */
  async encryptMessage(
    plaintext: string,
    sessionState: DoubleRatchetState
  ): Promise<{ encrypted: EncryptedMessage; newState: DoubleRatchetState }> {
    try {
      // Step 1: Advance the sending chain
      const messageKey = await this.deriveMessageKey(sessionState.chainKeySend);
      const newChainKey = await this.advanceChainKey(sessionState.chainKeySend);
      
      // Step 2: Generate nonce
      const nonce = Nonce.generate();
      
      // Step 3: Encrypt the message
      const plaintextBytes = new TextEncoder().encode(plaintext);
      const encrypted = await this.encryptWithAESGCM(
        plaintextBytes,
        messageKey.key,
        nonce.toUint8Array()
      );
      
      // Step 4: Create encrypted message
      const encryptedMessage: EncryptedMessage = {
        id: crypto.randomUUID(),
        senderId: '', // Will be set by calling service
        recipientId: '', // Will be set by calling service
        ciphertext: new CipherText(encrypted.ciphertext),
        nonce: nonce,
        authTag: new AuthenticationTag(encrypted.authTag),
        timestamp: new Date(),
        messageNumber: sessionState.sendMessageNumber,
        chainKey: newChainKey
      };
      
      // Step 5: Update session state
      const newState: DoubleRatchetState = {
        ...sessionState,
        chainKeySend: newChainKey,
        sendMessageNumber: sessionState.sendMessageNumber + 1
      };
      
      return { encrypted: encryptedMessage, newState };
    } catch (error) {
      throw new CryptoError(
        `Failed to encrypt message: ${error.message}`,
        'ENCRYPTION_FAILED'
      );
    }
  }

  /**
   * Decrypt a message using the Double Ratchet algorithm
   */
  async decryptMessage(
    encrypted: EncryptedMessage,
    sessionState: DoubleRatchetState
  ): Promise<{ plaintext: string; newState: DoubleRatchetState }> {
    try {
      // Step 1: Check for skipped messages
      const messageKey = await this.getMessageKey(encrypted, sessionState);
      
      // Step 2: Decrypt the message
      const decrypted = await this.decryptWithAESGCM(
        encrypted.ciphertext.toUint8Array(),
        messageKey.key,
        encrypted.nonce.toUint8Array(),
        encrypted.authTag.toUint8Array()
      );
      
      // Step 3: Convert to string
      const plaintext = new TextDecoder().decode(decrypted);
      
      // Step 4: Update session state
      const newState = await this.updateReceiveState(encrypted, sessionState);
      
      return { plaintext, newState };
    } catch (error) {
      throw new CryptoError(
        `Failed to decrypt message: ${error.message}`,
        'DECRYPTION_FAILED'
      );
    }
  }

  /**
   * Perform Diffie-Hellman key exchange
   */
  async performDH(
    privateKey: Uint8Array,
    publicKey: Uint8Array
  ): Promise<Uint8Array> {
    try {
      const privateKeyObj = await crypto.subtle.importKey(
        'raw',
        privateKey,
        { name: 'X25519' },
        false,
        ['deriveBits']
      );
      
      const publicKeyObj = await crypto.subtle.importKey(
        'raw',
        publicKey,
        { name: 'X25519' },
        false,
        []
      );
      
      const sharedSecret = await crypto.subtle.deriveBits(
        { name: 'X25519', public: publicKeyObj },
        privateKeyObj,
        256
      );
      
      return new Uint8Array(sharedSecret);
    } catch (error) {
      throw new CryptoError(
        `DH key exchange failed: ${error.message}`,
        'DH_FAILED'
      );
    }
  }

  /**
   * Generate a new ephemeral key pair
   */
  async generateEphemeralKeyPair(): Promise<EphemeralKey> {
    try {
      const keyPair = await crypto.subtle.generateKey(
        { name: 'X25519' },
        true,
        ['deriveBits']
      );
      
      const publicKey = await crypto.subtle.exportKey('raw', keyPair.publicKey);
      const privateKey = await crypto.subtle.exportKey('raw', keyPair.privateKey);
      
      return {
        publicKey: new Uint8Array(publicKey),
        privateKey: new Uint8Array(privateKey)
      };
    } catch (error) {
      throw new CryptoError(
        `Failed to generate ephemeral key pair: ${error.message}`,
        'KEY_GENERATION_FAILED'
      );
    }
  }

  /**
   * Derive a root key using HKDF
   */
  async deriveRootKey(
    rootKey: Uint8Array,
    dhOutput: Uint8Array
  ): Promise<{ newRootKey: Uint8Array; chainKey: Uint8Array }> {
    try {
      const ikm = new Uint8Array(rootKey.length + dhOutput.length);
      ikm.set(rootKey);
      ikm.set(dhOutput, rootKey.length);
      
      const salt = new Uint8Array(32); // Zero salt
      const info = new TextEncoder().encode('RootKey');
      
      const material = await this.hkdfExtract(salt, ikm);
      const expanded = await this.hkdfExpand(material, info, 64);
      
      return {
        newRootKey: expanded.slice(0, 32),
        chainKey: expanded.slice(32, 64)
      };
    } catch (error) {
      throw new CryptoError(
        `Failed to derive root key: ${error.message}`,
        'ROOT_KEY_DERIVATION_FAILED'
      );
    }
  }

  // Private helper methods

  private async encryptWithAESGCM(
    plaintext: Uint8Array,
    key: Uint8Array,
    nonce: Uint8Array
  ): Promise<{ ciphertext: Uint8Array; authTag: Uint8Array }> {
    const keyObj = await crypto.subtle.importKey(
      'raw',
      key,
      { name: this.constructor.ALGORITHM },
      false,
      ['encrypt']
    );
    
    const encrypted = await crypto.subtle.encrypt(
      { name: this.constructor.ALGORITHM, iv: nonce, tagLength: this.constructor.TAG_LENGTH * 8 },
      keyObj,
      plaintext
    );
    
    const encryptedArray = new Uint8Array(encrypted);
    const authTagStart = encryptedArray.length - this.constructor.TAG_LENGTH;
    
    return {
      ciphertext: encryptedArray.slice(0, authTagStart),
      authTag: encryptedArray.slice(authTagStart)
    };
  }

  private async decryptWithAESGCM(
    ciphertext: Uint8Array,
    key: Uint8Array,
    nonce: Uint8Array,
    authTag: Uint8Array
  ): Promise<Uint8Array> {
    const keyObj = await crypto.subtle.importKey(
      'raw',
      key,
      { name: this.constructor.ALGORITHM },
      false,
      ['decrypt']
    );
    
    const combined = new Uint8Array(ciphertext.length + authTag.length);
    combined.set(ciphertext);
    combined.set(authTag, ciphertext.length);
    
    const decrypted = await crypto.subtle.decrypt(
      { name: this.constructor.ALGORITHM, iv: nonce, tagLength: this.constructor.TAG_LENGTH * 8 },
      keyObj,
      combined
    );
    
    return new Uint8Array(decrypted);
  }

  private async deriveMessageKey(chainKey: Uint8Array): Promise<MessageKey> {
    const info = new TextEncoder().encode('MessageKey');
    const salt = new Uint8Array(32); // Zero salt
    
    const material = await this.hkdfExtract(salt, chainKey);
    const key = await this.hkdfExpand(material, info, this.constructor.KEY_LENGTH);
    
    return {
      key,
      messageNumber: 0, // Will be set by caller
      chainKey
    };
  }

  private async advanceChainKey(chainKey: Uint8Array): Promise<Uint8Array> {
    const hmacKey = await crypto.subtle.importKey(
      'raw',
      chainKey,
      { name: 'HMAC', hash: 'SHA-256' },
      false,
      ['sign']
    );
    
    const constant = new Uint8Array([0x01]);
    const signature = await crypto.subtle.sign('HMAC', hmacKey, constant);
    
    return new Uint8Array(signature);
  }

  private async getMessageKey(
    encrypted: EncryptedMessage,
    sessionState: DoubleRatchetState
  ): Promise<MessageKey> {
    // For simplicity, we'll derive the key from the chain key
    // In a full implementation, this would handle skipped messages
    return this.deriveMessageKey(sessionState.chainKeyReceive);
  }

  private async updateReceiveState(
    encrypted: EncryptedMessage,
    sessionState: DoubleRatchetState
  ): Promise<DoubleRatchetState> {
    const newChainKey = await this.advanceChainKey(sessionState.chainKeyReceive);
    
    return {
      ...sessionState,
      chainKeyReceive: newChainKey,
      receiveMessageNumber: sessionState.receiveMessageNumber + 1
    };
  }

  private async hkdfExtract(salt: Uint8Array, ikm: Uint8Array): Promise<Uint8Array> {
    const key = await crypto.subtle.importKey(
      'raw',
      salt,
      { name: 'HMAC', hash: 'SHA-256' },
      false,
      ['sign']
    );
    
    const signature = await crypto.subtle.sign('HMAC', key, ikm);
    return new Uint8Array(signature);
  }

  private async hkdfExpand(
    prk: Uint8Array,
    info: Uint8Array,
    length: number
  ): Promise<Uint8Array> {
    const key = await crypto.subtle.importKey(
      'raw',
      prk,
      { name: 'HMAC', hash: 'SHA-256' },
      false,
      ['sign']
    );
    
    const n = Math.ceil(length / 32); // SHA-256 output length
    const t = new Uint8Array(length);
    let tPrev = new Uint8Array(0);
    
    for (let i = 1; i <= n; i++) {
      const input = new Uint8Array(tPrev.length + info.length + 1);
      input.set(tPrev);
      input.set(info, tPrev.length);
      input[input.length - 1] = i;
      
      const signature = await crypto.subtle.sign('HMAC', key, input);
      const tCurrent = new Uint8Array(signature);
      
      const start = (i - 1) * 32;
      const end = Math.min(start + 32, length);
      t.set(tCurrent.slice(0, end - start), start);
      
      tPrev = tCurrent;
    }
    
    return t;
  }
}