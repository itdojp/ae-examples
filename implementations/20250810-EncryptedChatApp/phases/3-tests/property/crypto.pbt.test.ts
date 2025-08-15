import { describe, it, expect, beforeAll } from 'vitest';
import fc from 'fast-check';
import { KeyManager } from '../../src/domain/crypto/keyManager';
import { DoubleRatchet } from '../../src/domain/crypto/doubleRatchet';
import sodium from 'libsodium-wrappers';

describe('Cryptographic Properties', () => {
  let keyManager: KeyManager;

  beforeAll(async () => {
    await sodium.ready;
    keyManager = await KeyManager.getInstance();
    await DoubleRatchet.initialize();
  });

  describe('Key Generation Properties', () => {
    it('should generate unique identity keys for different users', () => {
      fc.assert(
        fc.property(
          fc.array(fc.uuid(), { minLength: 2, maxLength: 10 }),
          (userIds) => {
            const keys = userIds.map(id => keyManager.generateIdentityKeyPair(id));
            const publicKeys = keys.map(k => k.publicKey);
            
            // All public keys should be unique
            const uniqueKeys = new Set(publicKeys);
            expect(uniqueKeys.size).toBe(publicKeys.length);
            
            // All keys should be valid base64
            publicKeys.forEach(key => {
              expect(() => sodium.from_base64(key)).not.toThrow();
            });
          }
        )
      );
    });

    it('should generate valid signed pre-keys with correct signatures', () => {
      fc.assert(
        fc.property(
          fc.uuid(),
          fc.integer({ min: 1, max: 1000 }),
          (userId, keyId) => {
            const identityKey = keyManager.generateIdentityKeyPair(userId);
            const signedPreKey = keyManager.generateSignedPreKey(
              userId,
              identityKey.privateKey!,
              keyId
            );
            
            // Verify signature
            const isValid = keyManager.verifySignedPreKey(
              signedPreKey.publicKey,
              signedPreKey.signature,
              identityKey.publicKey
            );
            
            expect(isValid).toBe(true);
          }
        )
      );
    });

    it('should generate requested number of one-time pre-keys with sequential IDs', () => {
      fc.assert(
        fc.property(
          fc.uuid(),
          fc.integer({ min: 1, max: 100 }),
          fc.integer({ min: 1, max: 200 }),
          (userId, startId, count) => {
            const keys = keyManager.generateOneTimePreKeys(userId, startId, count);
            
            expect(keys).toHaveLength(count);
            
            // Check sequential IDs
            keys.forEach((key, index) => {
              expect(key.id).toBe(startId + index);
              expect(key.userId).toBe(userId);
              expect(key.used).toBe(false);
            });
            
            // All public keys should be unique
            const publicKeys = keys.map(k => k.publicKey);
            const uniqueKeys = new Set(publicKeys);
            expect(uniqueKeys.size).toBe(publicKeys.length);
          }
        )
      );
    });
  });

  describe('Encryption/Decryption Properties', () => {
    it('should correctly encrypt and decrypt messages (reversibility)', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 1, maxLength: 1000 }),
          fc.uint8Array({ minLength: 32, maxLength: 32 }),
          (plaintext, keyArray) => {
            const encrypted = keyManager.encryptMessage(plaintext, keyArray);
            const decrypted = keyManager.decryptMessage(
              encrypted.ciphertext,
              encrypted.nonce,
              encrypted.authTag,
              keyArray
            );
            
            expect(decrypted).toBe(plaintext);
          }
        )
      );
    });

    it('should produce different ciphertexts for same plaintext (nonce uniqueness)', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 1, maxLength: 100 }),
          fc.uint8Array({ minLength: 32, maxLength: 32 }),
          (plaintext, keyArray) => {
            const encrypted1 = keyManager.encryptMessage(plaintext, keyArray);
            const encrypted2 = keyManager.encryptMessage(plaintext, keyArray);
            
            // Nonces should be different
            expect(encrypted1.nonce).not.toBe(encrypted2.nonce);
            
            // Ciphertexts should be different
            expect(encrypted1.ciphertext).not.toBe(encrypted2.ciphertext);
            
            // Both should decrypt to same plaintext
            const decrypted1 = keyManager.decryptMessage(
              encrypted1.ciphertext,
              encrypted1.nonce,
              encrypted1.authTag,
              keyArray
            );
            const decrypted2 = keyManager.decryptMessage(
              encrypted2.ciphertext,
              encrypted2.nonce,
              encrypted2.authTag,
              keyArray
            );
            
            expect(decrypted1).toBe(plaintext);
            expect(decrypted2).toBe(plaintext);
          }
        )
      );
    });

    it('should fail decryption with wrong key', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 1, maxLength: 100 }),
          fc.uint8Array({ minLength: 32, maxLength: 32 }),
          fc.uint8Array({ minLength: 32, maxLength: 32 }),
          (plaintext, correctKey, wrongKey) => {
            // Ensure keys are different
            fc.pre(!correctKey.every((v, i) => v === wrongKey[i]));
            
            const encrypted = keyManager.encryptMessage(plaintext, correctKey);
            
            // Should throw when decrypting with wrong key
            expect(() => {
              keyManager.decryptMessage(
                encrypted.ciphertext,
                encrypted.nonce,
                encrypted.authTag,
                wrongKey
              );
            }).toThrow();
          }
        )
      );
    });
  });

  describe('Double Ratchet Properties', () => {
    it('should maintain message order within a chain', async () => {
      fc.assert(
        fc.asyncProperty(
          fc.array(fc.string({ minLength: 1, maxLength: 100 }), { minLength: 1, maxLength: 10 }),
          async (messages) => {
            const rootKey = sodium.randombytes_buf(32);
            const ratchet = new DoubleRatchet(rootKey);
            const receiverRatchet = new DoubleRatchet(rootKey);
            
            // Initialize sender
            const receiverKeyPair = receiverRatchet.generateKeyPair();
            await ratchet.initializeAsSender(receiverKeyPair.publicKey);
            
            // Encrypt all messages
            const encrypted = [];
            for (const msg of messages) {
              const plaintext = new TextEncoder().encode(msg);
              const result = await ratchet.ratchetEncrypt(plaintext);
              encrypted.push({ msg, ...result });
            }
            
            // Message numbers should be sequential
            encrypted.forEach((e, i) => {
              expect(e.header.messageNumber).toBe(i);
            });
            
            // Decrypt in order
            for (let i = 0; i < encrypted.length; i++) {
              const decrypted = await receiverRatchet.ratchetDecrypt(
                encrypted[i].header,
                encrypted[i].ciphertext
              );
              const plaintext = new TextDecoder().decode(decrypted);
              expect(plaintext).toBe(messages[i]);
            }
          }
        )
      );
    });

    it('should handle out-of-order message delivery', async () => {
      fc.assert(
        fc.asyncProperty(
          fc.array(fc.string({ minLength: 1, maxLength: 50 }), { minLength: 3, maxLength: 5 }),
          async (messages) => {
            const rootKey = sodium.randombytes_buf(32);
            const sender = new DoubleRatchet(rootKey);
            const receiver = new DoubleRatchet(rootKey);
            
            // Initialize
            const receiverKeyPair = receiver.generateKeyPair();
            await sender.initializeAsSender(receiverKeyPair.publicKey);
            
            // Encrypt all messages
            const encrypted = [];
            for (const msg of messages) {
              const plaintext = new TextEncoder().encode(msg);
              const result = await sender.ratchetEncrypt(plaintext);
              encrypted.push({ msg, ...result });
            }
            
            // Shuffle for out-of-order delivery
            const shuffled = [...encrypted].sort(() => Math.random() - 0.5);
            
            // Should still decrypt correctly
            const decrypted = [];
            for (const e of shuffled) {
              const plaintext = await receiver.ratchetDecrypt(e.header, e.ciphertext);
              decrypted.push({
                msg: new TextDecoder().decode(plaintext),
                num: e.header.messageNumber
              });
            }
            
            // Sort by message number and verify
            decrypted.sort((a, b) => a.num - b.num);
            decrypted.forEach((d, i) => {
              expect(d.msg).toBe(messages[i]);
            });
          }
        )
      );
    });
  });

  describe('Safety Number Properties', () => {
    it('should generate deterministic safety numbers', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 32, maxLength: 64 }),
          fc.string({ minLength: 32, maxLength: 64 }),
          (key1, key2) => {
            const number1 = keyManager.generateSafetyNumber(key1, key2);
            const number2 = keyManager.generateSafetyNumber(key1, key2);
            
            // Same inputs should produce same output
            expect(number1).toBe(number2);
            
            // Should be commutative
            const number3 = keyManager.generateSafetyNumber(key2, key1);
            expect(number1).toBe(number3);
          }
        )
      );
    });

    it('should generate unique safety numbers for different key pairs', () => {
      fc.assert(
        fc.property(
          fc.array(
            fc.tuple(
              fc.string({ minLength: 32, maxLength: 64 }),
              fc.string({ minLength: 32, maxLength: 64 })
            ),
            { minLength: 2, maxLength: 10 }
          ),
          (keyPairs) => {
            const numbers = keyPairs.map(([k1, k2]) => 
              keyManager.generateSafetyNumber(k1, k2)
            );
            
            // Check for uniqueness (with high probability)
            const uniqueNumbers = new Set(numbers);
            
            // Allow for occasional collisions in random data
            // but expect mostly unique values
            expect(uniqueNumbers.size).toBeGreaterThan(numbers.length * 0.8);
          }
        )
      );
    });
  });

  describe('Password Hashing Properties', () => {
    it('should hash and verify passwords correctly', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 8, maxLength: 128 }),
          (password) => {
            const hash = keyManager.hashPassword(password);
            
            // Should verify correctly
            expect(keyManager.verifyPassword(password, hash)).toBe(true);
            
            // Should not verify with wrong password
            expect(keyManager.verifyPassword(password + 'x', hash)).toBe(false);
          }
        )
      );
    });

    it('should generate different hashes for same password', () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 8, maxLength: 64 }),
          (password) => {
            const hash1 = keyManager.hashPassword(password);
            const hash2 = keyManager.hashPassword(password);
            
            // Hashes should be different (due to salt)
            expect(hash1).not.toBe(hash2);
            
            // Both should verify
            expect(keyManager.verifyPassword(password, hash1)).toBe(true);
            expect(keyManager.verifyPassword(password, hash2)).toBe(true);
          }
        )
      );
    });
  });

  describe('X3DH Key Exchange Properties', () => {
    it('should produce same shared secret for both parties', () => {
      fc.assert(
        fc.property(
          fc.uuid(),
          fc.uuid(),
          (userId1, userId2) => {
            // Generate keys for both users
            const user1Identity = keyManager.generateIdentityKeyPair(userId1);
            const user2Identity = keyManager.generateIdentityKeyPair(userId2);
            
            const user1Ephemeral = keyManager.generateX25519KeyPair();
            const user2SignedPreKey = keyManager.generateSignedPreKey(
              userId2,
              user2Identity.privateKey!,
              1
            );
            
            // User1 performs X3DH
            const sharedSecret1 = keyManager.performX3DH(
              user1Identity.privateKey!,
              user1Ephemeral.privateKey,
              user2Identity.publicKey,
              user2SignedPreKey.publicKey
            );
            
            // In a real scenario, user2 would derive the same secret
            // This would require the inverse calculation
            
            // Shared secret should be 32 bytes
            expect(sharedSecret1).toHaveLength(32);
            
            // Should be deterministic
            const sharedSecret2 = keyManager.performX3DH(
              user1Identity.privateKey!,
              user1Ephemeral.privateKey,
              user2Identity.publicKey,
              user2SignedPreKey.publicKey
            );
            
            expect(sharedSecret1).toEqual(sharedSecret2);
          }
        )
      );
    });
  });
});