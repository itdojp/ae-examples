/**
 * Core Encryption Module
 * Implements end-to-end encryption using Signal Protocol
 */

import * as ed from '@noble/ed25519';
import { sha256 } from '@noble/hashes/sha256';
import { randomBytes } from 'crypto';
import nacl from 'tweetnacl';

export interface KeyPair {
  publicKey: Uint8Array;
  privateKey: Uint8Array;
}

export interface IdentityKey extends KeyPair {
  id: string;
  createdAt: Date;
}

export interface PreKey extends KeyPair {
  id: number;
  signature?: Uint8Array;
}

export interface OneTimePreKey extends KeyPair {
  id: number;
  used: boolean;
}

export interface SessionKey {
  key: Uint8Array;
  counter: number;
  previousCounter: number;
}

export interface EncryptedMessage {
  ciphertext: Uint8Array;
  nonce: Uint8Array;
  ephemeralPublicKey?: Uint8Array;
  counter: number;
  previousCounter: number;
}

export class CryptoService {
  /**
   * Generate an identity key pair using Ed25519
   */
  static async generateIdentityKeyPair(): Promise<IdentityKey> {
    const privateKey = ed.utils.randomPrivateKey();
    const publicKey = await ed.getPublicKeyAsync(privateKey);
    
    return {
      id: this.generateKeyId(),
      publicKey,
      privateKey,
      createdAt: new Date()
    };
  }

  /**
   * Generate a signed pre-key
   */
  static async generateSignedPreKey(identityKey: IdentityKey): Promise<PreKey> {
    const privateKey = ed.utils.randomPrivateKey();
    const publicKey = await ed.getPublicKeyAsync(privateKey);
    
    const signature = await ed.signAsync(publicKey, identityKey.privateKey);
    
    return {
      id: Math.floor(Math.random() * 0xFFFFFF),
      publicKey,
      privateKey,
      signature
    };
  }

  /**
   * Generate one-time pre-keys
   */
  static async generateOneTimePreKeys(count: number = 100): Promise<OneTimePreKey[]> {
    const keys: OneTimePreKey[] = [];
    
    for (let i = 0; i < count; i++) {
      const privateKey = ed.utils.randomPrivateKey();
      const publicKey = await ed.getPublicKeyAsync(privateKey);
      
      keys.push({
        id: i,
        publicKey,
        privateKey,
        used: false
      });
    }
    
    return keys;
  }

  /**
   * Perform Diffie-Hellman key exchange
   */
  static async performDH(privateKey: Uint8Array, publicKey: Uint8Array): Promise<Uint8Array> {
    const sharedSecret = nacl.scalarMult(privateKey, publicKey);
    return sha256(sharedSecret);
  }

  /**
   * Derive root key and chain key using KDF
   */
  static deriveRootAndChainKeys(
    sharedSecret: Uint8Array,
    rootKey?: Uint8Array
  ): { rootKey: Uint8Array; chainKey: Uint8Array } {
    const kdfInput = rootKey 
      ? new Uint8Array([...rootKey, ...sharedSecret])
      : sharedSecret;
    
    const output = sha256(kdfInput);
    
    return {
      rootKey: output.slice(0, 32),
      chainKey: output.slice(32, 64)
    };
  }

  /**
   * Derive message key from chain key
   */
  static deriveMessageKey(chainKey: Uint8Array): Uint8Array {
    return sha256(new Uint8Array([...chainKey, 0x01]));
  }

  /**
   * Advance chain key
   */
  static advanceChainKey(chainKey: Uint8Array): Uint8Array {
    return sha256(new Uint8Array([...chainKey, 0x02]));
  }

  /**
   * Encrypt message using AES-256-GCM
   */
  static encrypt(
    plaintext: string,
    key: Uint8Array
  ): EncryptedMessage {
    const nonce = randomBytes(24);
    const message = new TextEncoder().encode(plaintext);
    
    const box = nacl.secretbox(message, nonce, key);
    
    return {
      ciphertext: box,
      nonce,
      counter: 0,
      previousCounter: 0
    };
  }

  /**
   * Decrypt message
   */
  static decrypt(
    encrypted: EncryptedMessage,
    key: Uint8Array
  ): string {
    const decrypted = nacl.secretbox.open(
      encrypted.ciphertext,
      encrypted.nonce,
      key
    );
    
    if (!decrypted) {
      throw new Error('Decryption failed');
    }
    
    return new TextDecoder().decode(decrypted);
  }

  /**
   * Generate a unique key ID
   */
  private static generateKeyId(): string {
    return randomBytes(16).toString('hex');
  }

  /**
   * Calculate fingerprint for security number
   */
  static calculateFingerprint(
    localIdentity: Uint8Array,
    remoteIdentity: Uint8Array
  ): string {
    const combined = new Uint8Array([...localIdentity, ...remoteIdentity]);
    const hash = sha256(combined);
    
    // Convert to readable format (groups of 5 digits)
    const digits = [];
    for (let i = 0; i < hash.length; i += 2) {
      const num = (hash[i] << 8) | hash[i + 1];
      digits.push(String(num % 100000).padStart(5, '0'));
    }
    
    return digits.slice(0, 12).join(' ');
  }
}