/**
 * Double Ratchet Algorithm Implementation
 * Provides Perfect Forward Secrecy and Future Secrecy
 */

import { CryptoService, KeyPair, EncryptedMessage } from './encryption.js';
import { randomBytes } from 'crypto';

export interface RatchetHeader {
  dhPublicKey: Uint8Array;
  previousChainCount: number;
  messageNumber: number;
}

export interface RatchetState {
  dhSelf: KeyPair;
  dhRemote?: Uint8Array;
  rootKey: Uint8Array;
  chainKeySend?: Uint8Array;
  chainKeyRecv?: Uint8Array;
  messageSendCount: number;
  messageRecvCount: number;
  previousSendingChainCount: number;
  skippedMessageKeys: Map<string, Uint8Array>;
}

export interface RatchetMessage {
  header: RatchetHeader;
  ciphertext: Uint8Array;
  nonce: Uint8Array;
}

export class DoubleRatchet {
  private state: RatchetState;
  private readonly maxSkip = 1000;

  constructor(
    sharedSecret: Uint8Array,
    isInitiator: boolean,
    remotePublicKey?: Uint8Array
  ) {
    const dhKeyPair = this.generateDHKeyPair();
    
    this.state = {
      dhSelf: dhKeyPair,
      dhRemote: remotePublicKey,
      rootKey: sharedSecret,
      messageSendCount: 0,
      messageRecvCount: 0,
      previousSendingChainCount: 0,
      skippedMessageKeys: new Map()
    };

    if (isInitiator && remotePublicKey) {
      this.dhRatchet(remotePublicKey);
    }
  }

  /**
   * Encrypt a message using the Double Ratchet
   */
  async encrypt(plaintext: string): Promise<RatchetMessage> {
    if (!this.state.chainKeySend) {
      throw new Error('Sending chain not initialized');
    }

    const messageKey = CryptoService.deriveMessageKey(this.state.chainKeySend);
    this.state.chainKeySend = CryptoService.advanceChainKey(this.state.chainKeySend);
    
    const encrypted = CryptoService.encrypt(plaintext, messageKey);
    
    const header: RatchetHeader = {
      dhPublicKey: this.state.dhSelf.publicKey,
      previousChainCount: this.state.previousSendingChainCount,
      messageNumber: this.state.messageSendCount
    };
    
    this.state.messageSendCount++;
    
    return {
      header,
      ciphertext: encrypted.ciphertext,
      nonce: encrypted.nonce
    };
  }

  /**
   * Decrypt a message using the Double Ratchet
   */
  async decrypt(message: RatchetMessage): Promise<string> {
    // Try skipped message keys first
    const skippedKey = this.trySkippedMessageKeys(message);
    if (skippedKey) {
      return CryptoService.decrypt(
        {
          ciphertext: message.ciphertext,
          nonce: message.nonce,
          counter: 0,
          previousCounter: 0
        },
        skippedKey
      );
    }

    // Check if we need to perform DH ratchet
    if (!this.state.dhRemote || 
        !this.arraysEqual(message.header.dhPublicKey, this.state.dhRemote)) {
      this.skipMessageKeys(message.header.previousChainCount);
      this.dhRatchet(message.header.dhPublicKey);
    }

    // Skip any missing messages
    this.skipMessageKeys(message.header.messageNumber);

    if (!this.state.chainKeyRecv) {
      throw new Error('Receiving chain not initialized');
    }

    const messageKey = CryptoService.deriveMessageKey(this.state.chainKeyRecv);
    this.state.chainKeyRecv = CryptoService.advanceChainKey(this.state.chainKeyRecv);
    this.state.messageRecvCount++;

    return CryptoService.decrypt(
      {
        ciphertext: message.ciphertext,
        nonce: message.nonce,
        counter: 0,
        previousCounter: 0
      },
      messageKey
    );
  }

  /**
   * Perform DH ratchet step
   */
  private async dhRatchet(dhPublicKey: Uint8Array): Promise<void> {
    this.state.previousSendingChainCount = this.state.messageSendCount;
    this.state.messageSendCount = 0;
    this.state.messageRecvCount = 0;
    this.state.dhRemote = dhPublicKey;

    // Calculate shared secret
    const sharedSecret = await CryptoService.performDH(
      this.state.dhSelf.privateKey,
      dhPublicKey
    );

    // Derive new root and receiving chain keys
    const recvKeys = CryptoService.deriveRootAndChainKeys(
      sharedSecret,
      this.state.rootKey
    );
    this.state.rootKey = recvKeys.rootKey;
    this.state.chainKeyRecv = recvKeys.chainKey;

    // Generate new DH key pair
    this.state.dhSelf = this.generateDHKeyPair();

    // Calculate new shared secret for sending
    const sendSharedSecret = await CryptoService.performDH(
      this.state.dhSelf.privateKey,
      dhPublicKey
    );

    // Derive new sending chain key
    const sendKeys = CryptoService.deriveRootAndChainKeys(
      sendSharedSecret,
      this.state.rootKey
    );
    this.state.rootKey = sendKeys.rootKey;
    this.state.chainKeySend = sendKeys.chainKey;
  }

  /**
   * Skip message keys for out-of-order messages
   */
  private skipMessageKeys(until: number): void {
    if (this.state.messageRecvCount + this.maxSkip < until) {
      throw new Error('Too many messages skipped');
    }

    if (!this.state.chainKeyRecv) {
      return;
    }

    while (this.state.messageRecvCount < until) {
      const messageKey = CryptoService.deriveMessageKey(this.state.chainKeyRecv);
      const key = `${this.state.dhRemote}-${this.state.messageRecvCount}`;
      this.state.skippedMessageKeys.set(key, messageKey);
      this.state.chainKeyRecv = CryptoService.advanceChainKey(this.state.chainKeyRecv);
      this.state.messageRecvCount++;
    }
  }

  /**
   * Try to decrypt using skipped message keys
   */
  private trySkippedMessageKeys(message: RatchetMessage): Uint8Array | null {
    const key = `${message.header.dhPublicKey}-${message.header.messageNumber}`;
    const messageKey = this.state.skippedMessageKeys.get(key);
    
    if (messageKey) {
      this.state.skippedMessageKeys.delete(key);
      return messageKey;
    }
    
    return null;
  }

  /**
   * Generate a new DH key pair
   */
  private generateDHKeyPair(): KeyPair {
    const privateKey = randomBytes(32);
    const publicKey = randomBytes(32); // Simplified for demo
    
    return { privateKey, publicKey };
  }

  /**
   * Compare two Uint8Arrays
   */
  private arraysEqual(a: Uint8Array, b: Uint8Array): boolean {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }

  /**
   * Get the current state for persistence
   */
  getState(): RatchetState {
    return { ...this.state };
  }

  /**
   * Restore from persisted state
   */
  static fromState(state: RatchetState): DoubleRatchet {
    const ratchet = Object.create(DoubleRatchet.prototype);
    ratchet.state = state;
    ratchet.maxSkip = 1000;
    return ratchet;
  }
}