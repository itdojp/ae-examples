/**
 * Encryption Module Tests
 */

import { describe, test, expect, beforeEach } from '@jest/globals';
import { CryptoService } from '../src/crypto/encryption';
import { DoubleRatchet } from '../src/crypto/double-ratchet';

describe('CryptoService', () => {
  describe('Key Generation', () => {
    test('should generate identity key pair', async () => {
      const keyPair = await CryptoService.generateIdentityKeyPair();
      
      expect(keyPair).toBeDefined();
      expect(keyPair.id).toBeDefined();
      expect(keyPair.publicKey).toBeInstanceOf(Uint8Array);
      expect(keyPair.privateKey).toBeInstanceOf(Uint8Array);
      expect(keyPair.publicKey.length).toBeGreaterThan(0);
      expect(keyPair.privateKey.length).toBeGreaterThan(0);
    });

    test('should generate signed pre-key with valid signature', async () => {
      const identityKey = await CryptoService.generateIdentityKeyPair();
      const signedPreKey = await CryptoService.generateSignedPreKey(identityKey);
      
      expect(signedPreKey).toBeDefined();
      expect(signedPreKey.id).toBeDefined();
      expect(signedPreKey.signature).toBeInstanceOf(Uint8Array);
      expect(signedPreKey.signature?.length).toBeGreaterThan(0);
    });

    test('should generate multiple one-time pre-keys', async () => {
      const count = 50;
      const keys = await CryptoService.generateOneTimePreKeys(count);
      
      expect(keys).toHaveLength(count);
      keys.forEach((key, index) => {
        expect(key.id).toBe(index);
        expect(key.publicKey).toBeInstanceOf(Uint8Array);
        expect(key.privateKey).toBeInstanceOf(Uint8Array);
        expect(key.used).toBe(false);
      });
    });
  });

  describe('Encryption and Decryption', () => {
    test('should encrypt and decrypt message correctly', () => {
      const plaintext = 'Hello, secure world!';
      const key = new Uint8Array(32);
      crypto.getRandomValues(key);
      
      const encrypted = CryptoService.encrypt(plaintext, key);
      expect(encrypted.ciphertext).toBeInstanceOf(Uint8Array);
      expect(encrypted.nonce).toBeInstanceOf(Uint8Array);
      
      const decrypted = CryptoService.decrypt(encrypted, key);
      expect(decrypted).toBe(plaintext);
    });

    test('should fail to decrypt with wrong key', () => {
      const plaintext = 'Secret message';
      const key1 = new Uint8Array(32);
      const key2 = new Uint8Array(32);
      crypto.getRandomValues(key1);
      crypto.getRandomValues(key2);
      
      const encrypted = CryptoService.encrypt(plaintext, key1);
      
      expect(() => {
        CryptoService.decrypt(encrypted, key2);
      }).toThrow('Decryption failed');
    });

    test('should handle empty messages', () => {
      const plaintext = '';
      const key = new Uint8Array(32);
      crypto.getRandomValues(key);
      
      const encrypted = CryptoService.encrypt(plaintext, key);
      const decrypted = CryptoService.decrypt(encrypted, key);
      
      expect(decrypted).toBe(plaintext);
    });

    test('should handle unicode messages', () => {
      const plaintext = '你好世界 🔒 Привет мир';
      const key = new Uint8Array(32);
      crypto.getRandomValues(key);
      
      const encrypted = CryptoService.encrypt(plaintext, key);
      const decrypted = CryptoService.decrypt(encrypted, key);
      
      expect(decrypted).toBe(plaintext);
    });
  });

  describe('Security Number', () => {
    test('should calculate consistent fingerprint', () => {
      const localIdentity = new Uint8Array(32);
      const remoteIdentity = new Uint8Array(32);
      crypto.getRandomValues(localIdentity);
      crypto.getRandomValues(remoteIdentity);
      
      const fingerprint1 = CryptoService.calculateFingerprint(
        localIdentity,
        remoteIdentity
      );
      const fingerprint2 = CryptoService.calculateFingerprint(
        localIdentity,
        remoteIdentity
      );
      
      expect(fingerprint1).toBe(fingerprint2);
      expect(fingerprint1).toMatch(/^\d{5}( \d{5}){11}$/);
    });

    test('should produce different fingerprints for different keys', () => {
      const identity1 = new Uint8Array(32);
      const identity2 = new Uint8Array(32);
      const identity3 = new Uint8Array(32);
      crypto.getRandomValues(identity1);
      crypto.getRandomValues(identity2);
      crypto.getRandomValues(identity3);
      
      const fingerprint1 = CryptoService.calculateFingerprint(identity1, identity2);
      const fingerprint2 = CryptoService.calculateFingerprint(identity1, identity3);
      
      expect(fingerprint1).not.toBe(fingerprint2);
    });
  });

  describe('Key Derivation', () => {
    test('should derive root and chain keys', () => {
      const sharedSecret = new Uint8Array(32);
      crypto.getRandomValues(sharedSecret);
      
      const keys = CryptoService.deriveRootAndChainKeys(sharedSecret);
      
      expect(keys.rootKey).toBeInstanceOf(Uint8Array);
      expect(keys.chainKey).toBeInstanceOf(Uint8Array);
      expect(keys.rootKey.length).toBe(32);
      expect(keys.chainKey.length).toBe(32);
    });

    test('should derive message key from chain key', () => {
      const chainKey = new Uint8Array(32);
      crypto.getRandomValues(chainKey);
      
      const messageKey = CryptoService.deriveMessageKey(chainKey);
      
      expect(messageKey).toBeInstanceOf(Uint8Array);
      expect(messageKey.length).toBe(32);
    });

    test('should advance chain key correctly', () => {
      const chainKey = new Uint8Array(32);
      crypto.getRandomValues(chainKey);
      
      const advanced1 = CryptoService.advanceChainKey(chainKey);
      const advanced2 = CryptoService.advanceChainKey(advanced1);
      
      expect(advanced1).not.toEqual(chainKey);
      expect(advanced2).not.toEqual(advanced1);
      expect(advanced2).not.toEqual(chainKey);
    });
  });
});

describe('DoubleRatchet', () => {
  let sharedSecret: Uint8Array;
  let aliceRatchet: DoubleRatchet;
  let bobRatchet: DoubleRatchet;

  beforeEach(() => {
    sharedSecret = new Uint8Array(32);
    crypto.getRandomValues(sharedSecret);
  });

  test('should initialize ratchet for initiator and responder', () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    bobRatchet = new DoubleRatchet(sharedSecret, false);
    
    expect(aliceRatchet).toBeDefined();
    expect(bobRatchet).toBeDefined();
  });

  test('should encrypt and decrypt messages in order', async () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    bobRatchet = new DoubleRatchet(sharedSecret, false);
    
    const messages = [
      'First message',
      'Second message',
      'Third message'
    ];
    
    for (const plaintext of messages) {
      const encrypted = await aliceRatchet.encrypt(plaintext);
      const decrypted = await bobRatchet.decrypt(encrypted);
      expect(decrypted).toBe(plaintext);
    }
  });

  test('should handle bidirectional communication', async () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    bobRatchet = new DoubleRatchet(sharedSecret, false);
    
    // Alice sends to Bob
    const aliceMsg1 = await aliceRatchet.encrypt('Hello from Alice');
    const bobReceived1 = await bobRatchet.decrypt(aliceMsg1);
    expect(bobReceived1).toBe('Hello from Alice');
    
    // Bob sends to Alice
    const bobMsg1 = await bobRatchet.encrypt('Hello from Bob');
    const aliceReceived1 = await aliceRatchet.decrypt(bobMsg1);
    expect(aliceReceived1).toBe('Hello from Bob');
    
    // Alice sends again
    const aliceMsg2 = await aliceRatchet.encrypt('Second from Alice');
    const bobReceived2 = await bobRatchet.decrypt(aliceMsg2);
    expect(bobReceived2).toBe('Second from Alice');
  });

  test('should handle out-of-order messages', async () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    bobRatchet = new DoubleRatchet(sharedSecret, false);
    
    // Alice sends multiple messages
    const msg1 = await aliceRatchet.encrypt('Message 1');
    const msg2 = await aliceRatchet.encrypt('Message 2');
    const msg3 = await aliceRatchet.encrypt('Message 3');
    
    // Bob receives out of order
    const decrypted3 = await bobRatchet.decrypt(msg3);
    const decrypted1 = await bobRatchet.decrypt(msg1);
    const decrypted2 = await bobRatchet.decrypt(msg2);
    
    expect(decrypted1).toBe('Message 1');
    expect(decrypted2).toBe('Message 2');
    expect(decrypted3).toBe('Message 3');
  });

  test('should maintain state for persistence', async () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    
    const msg1 = await aliceRatchet.encrypt('Before save');
    const state = aliceRatchet.getState();
    
    // Restore from state
    const restoredRatchet = DoubleRatchet.fromState(state);
    const msg2 = await restoredRatchet.encrypt('After restore');
    
    expect(msg2).toBeDefined();
    expect(msg2.header.messageNumber).toBeGreaterThan(msg1.header.messageNumber);
  });

  test('should provide Perfect Forward Secrecy', async () => {
    const bobPublicKey = new Uint8Array(32);
    crypto.getRandomValues(bobPublicKey);
    
    aliceRatchet = new DoubleRatchet(sharedSecret, true, bobPublicKey);
    bobRatchet = new DoubleRatchet(sharedSecret, false);
    
    // Exchange some messages
    const msg1 = await aliceRatchet.encrypt('Message 1');
    await bobRatchet.decrypt(msg1);
    
    const msg2 = await bobRatchet.encrypt('Message 2');
    await aliceRatchet.decrypt(msg2);
    
    // Get states after key rotation
    const aliceState1 = aliceRatchet.getState();
    const bobState1 = bobRatchet.getState();
    
    // Continue messaging
    const msg3 = await aliceRatchet.encrypt('Message 3');
    await bobRatchet.decrypt(msg3);
    
    const aliceState2 = aliceRatchet.getState();
    const bobState2 = bobRatchet.getState();
    
    // Keys should have changed
    expect(aliceState2.rootKey).not.toEqual(aliceState1.rootKey);
    expect(bobState2.rootKey).not.toEqual(bobState1.rootKey);
  });
});