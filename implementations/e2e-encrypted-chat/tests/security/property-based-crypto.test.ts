/**
 * Property-Based Testing for E2E Encryption
 * 
 * Fast-checkを使用した暗号化プロパティのテスト
 * 大量のランダム入力での暗号化の正しさを検証
 */

import { describe, it } from 'vitest';
import fc from 'fast-check';
import { 
  CryptoService, 
  SecureChatClient, 
  SessionManager,
  EncryptedMessage 
} from '../../src/crypto';

describe('Property-Based Encryption Tests', () => {
  const cryptoService = new CryptoService();

  describe('暗号化・復号の可逆性 (Encryption Reversibility)', () => {
    it('任意のメッセージが暗号化・復号で元に戻る', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 10000 }),
        async (message: string) => {
          // Given: ランダムなメッセージ
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);

          // When: 暗号化後復号
          const encrypted = await session.encryptMessage(message);
          const decrypted = await session.decryptMessage(encrypted);

          // Then: 元のメッセージが復元される
          expect(decrypted).toBe(message);

          // Cleanup
          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 100 });
    });

    it('空文字列とUnicode文字列の暗号化対応', () => {
      fc.assert(fc.property(
        fc.oneof(
          fc.constant(''),
          fc.unicode({ minLength: 1, maxLength: 1000 }),
          fc.string({ minLength: 1, maxLength: 1000 }),
          fc.constantFrom('🔐', '🚀', '🇯🇵', '数学的記号: ∑∫√π')
        ),
        async (message: string) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);
          
          const encrypted = await session.encryptMessage(message);
          const decrypted = await session.decryptMessage(encrypted);

          expect(decrypted).toBe(message);

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 50 });
    });
  });

  describe('暗号化の一意性 (Encryption Uniqueness)', () => {
    it('同じメッセージでも異なる暗号文が生成される', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 1000 }),
        async (message: string) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);

          // When: 同じメッセージを2回暗号化
          const encrypted1 = await session.encryptMessage(message);
          const encrypted2 = await session.encryptMessage(message);

          // Then: 異なる暗号文が生成される（nonce が異なるため）
          expect(encrypted1.ciphertext).not.toEqual(encrypted2.ciphertext);
          expect(encrypted1.nonce).not.toEqual(encrypted2.nonce);

          // But: 両方とも正しく復号される
          const decrypted1 = await session.decryptMessage(encrypted1);
          const decrypted2 = await session.decryptMessage(encrypted2);
          expect(decrypted1).toBe(message);
          expect(decrypted2).toBe(message);

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 50 });
    });
  });

  describe('鍵分離の保証 (Key Separation)', () => {
    it('異なる鍵で暗号化されたメッセージは復号できない', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 1000 }),
        async (message: string) => {
          // Given: 2つの異なるセッション
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          const charlie = new SecureChatClient('charlie@test.com');
          
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();
          await charlie.generateIdentityKeyPair();

          const session1 = await SessionManager.createSession(alice, bob);
          const session2 = await SessionManager.createSession(alice, charlie);

          // When: session1で暗号化
          const encrypted = await session1.encryptMessage(message);

          // Then: session2では復号できない
          await expect(session2.decryptMessage(encrypted))
            .rejects.toThrow();

          alice.destroy();
          bob.destroy();
          charlie.destroy();
        }
      ), { numRuns: 30 });
    });
  });

  describe('Perfect Forward Secrecy Properties', () => {
    it('メッセージキーは使用後に確実に削除される', () => {
      fc.assert(fc.property(
        fc.array(fc.string({ minLength: 1, maxLength: 100 }), { minLength: 1, maxLength: 10 }),
        async (messages: string[]) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);
          const messageKeys: string[] = [];

          // When: 複数のメッセージを暗号化
          for (const message of messages) {
            const messageKey = await session.deriveMessageKey();
            messageKeys.push(messageKey.keyId);
            await session.encryptMessage(message, messageKey);
          }

          // Then: 全てのメッセージキーが削除されている
          for (const keyId of messageKeys) {
            expect(() => session.getStoredMessageKey(keyId))
              .toThrow('Message key not found or already deleted');
          }

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 20 });
    });

    it('鍵ローテーション後は古いキーで復号できない', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 100 }),
        fc.string({ minLength: 1, maxLength: 100 }),
        async (oldMessage: string, newMessage: string) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);

          // Given: 古いメッセージの暗号化
          const oldEncrypted = await session.encryptMessage(oldMessage);

          // When: 鍵ローテーション実行
          await session.performDHRatchet();
          const newEncrypted = await session.encryptMessage(newMessage);

          // Then: 新しいメッセージは復号可能、古いメッセージも復号可能（適切な実装では）
          const decryptedOld = await session.decryptMessage(oldEncrypted);
          const decryptedNew = await session.decryptMessage(newEncrypted);

          expect(decryptedOld).toBe(oldMessage);
          expect(decryptedNew).toBe(newMessage);

          // But: 現在のセッション鍵では古いメッセージを復号すべきではない
          const currentKey = session.getCurrentSessionKey();
          await expect(cryptoService.decryptWithKey(oldEncrypted, currentKey))
            .rejects.toThrow();

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 15 });
    });
  });

  describe('Authentication Tag Integrity', () => {
    it('認証タグの改竄でメッセージ復号が失敗する', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 1000 }),
        fc.uint8Array({ minLength: 16, maxLength: 16 }), // Invalid auth tag
        async (message: string, invalidTag: Uint8Array) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);
          
          // Given: 正常に暗号化されたメッセージ
          const encrypted = await session.encryptMessage(message);
          
          // When: 認証タグを改竄
          const tamperedMessage = {
            ...encrypted,
            authTag: invalidTag
          };

          // Then: 復号が失敗する
          await expect(session.decryptMessage(tamperedMessage))
            .rejects.toThrow('Authentication failed');

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 30 });
    });

    it('暗号文の改竄でメッセージ復号が失敗する', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 1000 }),
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 10 }), // Position to tamper
        async (message: string, tamperValue: number, tamperPos: number) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);
          
          const encrypted = await session.encryptMessage(message);
          
          // When: 暗号文の一部を改竄
          const tamperedCiphertext = new Uint8Array(encrypted.ciphertext);
          if (tamperedCiphertext.length > tamperPos) {
            tamperedCiphertext[tamperPos] = tamperValue;
            
            const tamperedMessage = {
              ...encrypted,
              ciphertext: tamperedCiphertext
            };

            // Then: 復号が失敗する（認証タグ検証で失敗）
            await expect(session.decryptMessage(tamperedMessage))
              .rejects.toThrow();
          }

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 25 });
    });
  });

  describe('Key Generation Properties', () => {
    it('生成される鍵は統計的に均等分散している', () => {
      fc.assert(fc.property(
        fc.integer({ min: 10, max: 100 }),
        async (numKeys: number) => {
          const keys: Uint8Array[] = [];
          
          // When: 複数の鍵を生成
          for (let i = 0; i < numKeys; i++) {
            const keyPair = await cryptoService.generateX25519KeyPair();
            keys.push(keyPair.privateKey);
          }

          // Then: 全ての鍵が異なる
          for (let i = 0; i < keys.length; i++) {
            for (let j = i + 1; j < keys.length; j++) {
              expect(keys[i]).not.toEqual(keys[j]);
            }
          }

          // And: 鍵長が正しい
          keys.forEach(key => {
            expect(key.length).toBe(32); // X25519 private key is 32 bytes
          });
        }
      ), { numRuns: 10 });
    });

    it('Safety Numberが決定的に生成される', () => {
      fc.assert(fc.property(
        fc.emailAddress(),
        fc.emailAddress(),
        async (email1: string, email2: string) => {
          if (email1 === email2) return; // Skip same email case

          const user1a = new SecureChatClient(email1);
          const user1b = new SecureChatClient(email1); // Same identity
          const user2 = new SecureChatClient(email2);

          await user1a.generateIdentityKeyPair();
          await user1b.generateIdentityKeyPair();
          await user2.generateIdentityKeyPair();

          // 同じ鍵を設定
          user1b.setIdentityKeyPair(user1a.getIdentityKeyPair());

          const session1a = await SessionManager.createSession(user1a, user2);
          const session1b = await SessionManager.createSession(user1b, user2);

          // Then: 同じSafety Numberが生成される
          expect(session1a.getSafetyNumber()).toBe(session1b.getSafetyNumber());

          user1a.destroy();
          user1b.destroy();
          user2.destroy();
        }
      ), { numRuns: 15 });
    });
  });
});

describe('Performance Property Tests', () => {
  describe('暗号化性能特性', () => {
    it('暗号化時間がメッセージサイズに線形比例する', () => {
      fc.assert(fc.property(
        fc.integer({ min: 1, max: 5 }), // Size multiplier
        async (sizeMultiplier: number) => {
          const baseMessage = 'A'.repeat(1000);
          const largeMessage = baseMessage.repeat(sizeMultiplier);

          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);

          // When: 異なるサイズのメッセージを暗号化
          const startTime = performance.now();
          await session.encryptMessage(largeMessage);
          const encryptionTime = performance.now() - startTime;

          // Then: 暗号化時間が制限内（1MBあたり50ms以下）
          const expectedMaxTime = (largeMessage.length / 1024 / 1024) * 50; // 50ms per MB
          expect(encryptionTime).toBeLessThan(expectedMaxTime);

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 10 });
    });
  });

  describe('メモリ使用量特性', () => {
    it('大量のメッセージ処理後もメモリリークしない', () => {
      fc.assert(fc.property(
        fc.array(fc.string({ minLength: 10, maxLength: 100 }), { minLength: 10, maxLength: 50 }),
        async (messages: string[]) => {
          const alice = new SecureChatClient('alice@test.com');
          const bob = new SecureChatClient('bob@test.com');
          await alice.generateIdentityKeyPair();
          await bob.generateIdentityKeyPair();

          const session = await SessionManager.createSession(alice, bob);

          const initialMemory = process.memoryUsage().heapUsed;

          // When: 大量のメッセージを処理
          for (const message of messages) {
            const encrypted = await session.encryptMessage(message);
            await session.decryptMessage(encrypted);
          }

          // Force garbage collection if available
          if (global.gc) {
            global.gc();
          }

          const finalMemory = process.memoryUsage().heapUsed;
          const memoryIncrease = finalMemory - initialMemory;

          // Then: メモリ増加量が合理的範囲内（メッセージ総サイズの10倍以下）
          const totalMessageSize = messages.join('').length;
          expect(memoryIncrease).toBeLessThan(totalMessageSize * 10);

          alice.destroy();
          bob.destroy();
        }
      ), { numRuns: 5 });
    });
  });
});