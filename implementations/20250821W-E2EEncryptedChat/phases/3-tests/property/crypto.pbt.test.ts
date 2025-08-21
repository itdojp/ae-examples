import fc from 'fast-check';
import { expect } from 'chai';
import * as crypto from 'crypto';

/**
 * E2E暗号化チャットアプリケーション - 暗号化プロパティベーステスト
 * 
 * Property-Based Testing を使用して暗号化機能の特性を検証します。
 * ランダムな入力に対して暗号化・復号の一貫性を確認します。
 */

describe('暗号化プロパティベーステスト', () => {
  
  // RSA キーペア生成のシミュレーション
  function generateRSAKeyPair(): { publicKey: string, privateKey: string } {
    const { publicKey, privateKey } = crypto.generateKeyPairSync('rsa', {
      modulusLength: 2048,
      publicKeyEncoding: { type: 'spki', format: 'pem' },
      privateKeyEncoding: { type: 'pkcs8', format: 'pem' }
    });
    
    return { publicKey, privateKey };
  }

  // AES キー生成
  function generateAESKey(): Buffer {
    return crypto.randomBytes(32); // 256-bit key
  }

  // RSA-OAEP 暗号化
  function rsaEncrypt(data: Buffer, publicKey: string): Buffer {
    return crypto.publicEncrypt({
      key: publicKey,
      padding: crypto.constants.RSA_PKCS1_OAEP_PADDING,
      oaepHash: 'sha256'
    }, data);
  }

  // RSA-OAEP 復号
  function rsaDecrypt(encryptedData: Buffer, privateKey: string): Buffer {
    return crypto.privateDecrypt({
      key: privateKey,
      padding: crypto.constants.RSA_PKCS1_OAEP_PADDING,
      oaepHash: 'sha256'
    }, encryptedData);
  }

  // AES-GCM 暗号化
  function aesGcmEncrypt(data: Buffer, key: Buffer): { encrypted: Buffer, iv: Buffer, tag: Buffer } {
    const iv = crypto.randomBytes(16);
    const cipher = crypto.createCipherGCM('aes-256-gcm', key);
    cipher.setAAD(Buffer.from('additional-auth-data'));
    
    const encrypted = Buffer.concat([
      cipher.update(data),
      cipher.final()
    ]);
    
    const tag = cipher.getAuthTag();
    
    return { encrypted, iv, tag };
  }

  // AES-GCM 復号
  function aesGcmDecrypt(encrypted: Buffer, key: Buffer, iv: Buffer, tag: Buffer): Buffer {
    const decipher = crypto.createDecipherGCM('aes-256-gcm', key);
    decipher.setAAD(Buffer.from('additional-auth-data'));
    decipher.setAuthTag(tag);
    
    return Buffer.concat([
      decipher.update(encrypted),
      decipher.final()
    ]);
  }

  describe('RSA-OAEP プロパティテスト', () => {
    
    it('property: 暗号化後の復号で元データが復元される', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 200 }), // RSA-2048の制限内
        (data) => {
          const { publicKey, privateKey } = generateRSAKeyPair();
          const dataBuffer = Buffer.from(data);
          
          const encrypted = rsaEncrypt(dataBuffer, publicKey);
          const decrypted = rsaDecrypt(encrypted, privateKey);
          
          expect(decrypted.equals(dataBuffer)).to.be.true;
        }
      ), { numRuns: 50 });
    });

    it('property: 同じデータの暗号化結果は毎回異なる（OAEP padding）', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 100 }),
        (data) => {
          const { publicKey } = generateRSAKeyPair();
          const dataBuffer = Buffer.from(data);
          
          const encrypted1 = rsaEncrypt(dataBuffer, publicKey);
          const encrypted2 = rsaEncrypt(dataBuffer, publicKey);
          
          // OAEPパディングにより、同じデータでも暗号化結果は異なる
          expect(encrypted1.equals(encrypted2)).to.be.false;
        }
      ), { numRuns: 30 });
    });

    it('property: 間違った秘密鍵では復号できない', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 100 }),
        (data) => {
          const { publicKey: publicKey1 } = generateRSAKeyPair();
          const { privateKey: privateKey2 } = generateRSAKeyPair();
          const dataBuffer = Buffer.from(data);
          
          const encrypted = rsaEncrypt(dataBuffer, publicKey1);
          
          expect(() => {
            rsaDecrypt(encrypted, privateKey2);
          }).to.throw();
        }
      ), { numRuns: 20 });
    });

    it('property: 暗号化データの改ざん検出', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 100 }),
        fc.integer({ min: 0, max: 255 }),
        (data, tamperByte) => {
          const { publicKey, privateKey } = generateRSAKeyPair();
          const dataBuffer = Buffer.from(data);
          
          const encrypted = rsaEncrypt(dataBuffer, publicKey);
          
          // ランダムな位置のバイトを改ざん
          const tamperPosition = Math.floor(Math.random() * encrypted.length);
          encrypted[tamperPosition] = tamperByte;
          
          expect(() => {
            rsaDecrypt(encrypted, privateKey);
          }).to.throw();
        }
      ), { numRuns: 30 });
    });
  });

  describe('AES-GCM プロパティテスト', () => {
    
    it('property: 暗号化後の復号で元データが復元される', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 0, maxLength: 10000 }),
        (data) => {
          const key = generateAESKey();
          const dataBuffer = Buffer.from(data);
          
          const { encrypted, iv, tag } = aesGcmEncrypt(dataBuffer, key);
          const decrypted = aesGcmDecrypt(encrypted, key, iv, tag);
          
          expect(decrypted.equals(dataBuffer)).to.be.true;
        }
      ), { numRuns: 100 });
    });

    it('property: 異なるキーでは復号できない', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 1000 }),
        (data) => {
          const key1 = generateAESKey();
          const key2 = generateAESKey();
          const dataBuffer = Buffer.from(data);
          
          const { encrypted, iv, tag } = aesGcmEncrypt(dataBuffer, key1);
          
          expect(() => {
            aesGcmDecrypt(encrypted, key2, iv, tag);
          }).to.throw();
        }
      ), { numRuns: 50 });
    });

    it('property: 認証タグの改ざん検出', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 1000 }),
        (data) => {
          const key = generateAESKey();
          const dataBuffer = Buffer.from(data);
          
          const { encrypted, iv, tag } = aesGcmEncrypt(dataBuffer, key);
          
          // 認証タグを改ざん
          const tamperedTag = Buffer.from(tag);
          tamperedTag[0] = tamperedTag[0] ^ 0xFF;
          
          expect(() => {
            aesGcmDecrypt(encrypted, key, iv, tamperedTag);
          }).to.throw();
        }
      ), { numRuns: 50 });
    });

    it('property: 暗号化データの改ざん検出', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 1000 }),
        (data) => {
          const key = generateAESKey();
          const dataBuffer = Buffer.from(data);
          
          const { encrypted, iv, tag } = aesGcmEncrypt(dataBuffer, key);
          
          // 暗号化データを改ざん
          const tamperedEncrypted = Buffer.from(encrypted);
          const tamperPosition = Math.floor(Math.random() * tamperedEncrypted.length);
          tamperedEncrypted[tamperPosition] = tamperedEncrypted[tamperPosition] ^ 0xFF;
          
          expect(() => {
            aesGcmDecrypt(tamperedEncrypted, key, iv, tag);
          }).to.throw();
        }
      ), { numRuns: 50 });
    });

    it('property: IVの改ざんで復号結果が変わる', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 1, maxLength: 1000 }),
        (data) => {
          const key = generateAESKey();
          const dataBuffer = Buffer.from(data);
          
          const { encrypted, iv, tag } = aesGcmEncrypt(dataBuffer, key);
          
          // IVを改ざん
          const tamperedIv = Buffer.from(iv);
          tamperedIv[0] = tamperedIv[0] ^ 0xFF;
          
          expect(() => {
            aesGcmDecrypt(encrypted, key, tamperedIv, tag);
          }).to.throw();
        }
      ), { numRuns: 30 });
    });
  });

  describe('E2E暗号化フロー プロパティテスト', () => {
    
    // E2E暗号化のシミュレーション
    function e2eEncrypt(message: Buffer, recipientPublicKey: string): {
      encryptedMessage: Buffer,
      encryptedAESKey: Buffer,
      iv: Buffer,
      tag: Buffer
    } {
      const aesKey = generateAESKey();
      const { encrypted: encryptedMessage, iv, tag } = aesGcmEncrypt(message, aesKey);
      const encryptedAESKey = rsaEncrypt(aesKey, recipientPublicKey);
      
      return { encryptedMessage, encryptedAESKey, iv, tag };
    }

    function e2eDecrypt(
      encryptedMessage: Buffer,
      encryptedAESKey: Buffer,
      iv: Buffer,
      tag: Buffer,
      recipientPrivateKey: string
    ): Buffer {
      const aesKey = rsaDecrypt(encryptedAESKey, recipientPrivateKey);
      return aesGcmDecrypt(encryptedMessage, aesKey, iv, tag);
    }

    it('property: E2E暗号化フロー全体の一貫性', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 1000 }),
        (message) => {
          const { publicKey, privateKey } = generateRSAKeyPair();
          const messageBuffer = Buffer.from(message, 'utf8');
          
          const { encryptedMessage, encryptedAESKey, iv, tag } = e2eEncrypt(messageBuffer, publicKey);
          const decryptedMessage = e2eDecrypt(encryptedMessage, encryptedAESKey, iv, tag, privateKey);
          
          expect(decryptedMessage.toString('utf8')).to.equal(message);
        }
      ), { numRuns: 100 });
    });

    it('property: マルチユーザー暗号化（同じメッセージ、異なる受信者）', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 500 }),
        (message) => {
          const alice = generateRSAKeyPair();
          const bob = generateRSAKeyPair();
          const messageBuffer = Buffer.from(message, 'utf8');
          
          const aliceEncryption = e2eEncrypt(messageBuffer, alice.publicKey);
          const bobEncryption = e2eEncrypt(messageBuffer, bob.publicKey);
          
          const aliceDecrypted = e2eDecrypt(
            aliceEncryption.encryptedMessage,
            aliceEncryption.encryptedAESKey,
            aliceEncryption.iv,
            aliceEncryption.tag,
            alice.privateKey
          );
          
          const bobDecrypted = e2eDecrypt(
            bobEncryption.encryptedMessage,
            bobEncryption.encryptedAESKey,
            bobEncryption.iv,
            bobEncryption.tag,
            bob.privateKey
          );
          
          expect(aliceDecrypted.toString('utf8')).to.equal(message);
          expect(bobDecrypted.toString('utf8')).to.equal(message);
          
          // Alice の暗号化データを Bob の鍵で復号しようとすると失敗
          expect(() => {
            e2eDecrypt(
              aliceEncryption.encryptedMessage,
              aliceEncryption.encryptedAESKey,
              aliceEncryption.iv,
              aliceEncryption.tag,
              bob.privateKey
            );
          }).to.throw();
        }
      ), { numRuns: 50 });
    });

    it('property: 暗号化の非決定性（同じメッセージでも暗号化結果は異なる）', () => {
      fc.assert(fc.property(
        fc.string({ minLength: 1, maxLength: 100 }),
        (message) => {
          const { publicKey, privateKey } = generateRSAKeyPair();
          const messageBuffer = Buffer.from(message, 'utf8');
          
          const encryption1 = e2eEncrypt(messageBuffer, publicKey);
          const encryption2 = e2eEncrypt(messageBuffer, publicKey);
          
          // 暗号化結果は毎回異なる（IVとAESキーがランダム）
          expect(encryption1.encryptedMessage.equals(encryption2.encryptedMessage)).to.be.false;
          expect(encryption1.encryptedAESKey.equals(encryption2.encryptedAESKey)).to.be.false;
          expect(encryption1.iv.equals(encryption2.iv)).to.be.false;
          
          // しかし両方とも正しく復号できる
          const decrypted1 = e2eDecrypt(
            encryption1.encryptedMessage,
            encryption1.encryptedAESKey,
            encryption1.iv,
            encryption1.tag,
            privateKey
          );
          
          const decrypted2 = e2eDecrypt(
            encryption2.encryptedMessage,
            encryption2.encryptedAESKey,
            encryption2.iv,
            encryption2.tag,
            privateKey
          );
          
          expect(decrypted1.toString('utf8')).to.equal(message);
          expect(decrypted2.toString('utf8')).to.equal(message);
        }
      ), { numRuns: 30 });
    });
  });

  describe('キー管理プロパティテスト', () => {
    
    it('property: キーペア生成の一意性', () => {
      fc.assert(fc.property(
        fc.integer({ min: 1, max: 10 }),
        (iterations) => {
          const keyPairs = [];
          
          for (let i = 0; i < iterations; i++) {
            keyPairs.push(generateRSAKeyPair());
          }
          
          // 全てのキーペアが異なることを確認
          for (let i = 0; i < keyPairs.length; i++) {
            for (let j = i + 1; j < keyPairs.length; j++) {
              expect(keyPairs[i].publicKey).to.not.equal(keyPairs[j].publicKey);
              expect(keyPairs[i].privateKey).to.not.equal(keyPairs[j].privateKey);
            }
          }
        }
      ), { numRuns: 20 });
    });

    it('property: AESキー生成の一意性とエントロピー', () => {
      fc.assert(fc.property(
        fc.integer({ min: 2, max: 100 }),
        (keyCount) => {
          const keys = [];
          
          for (let i = 0; i < keyCount; i++) {
            keys.push(generateAESKey());
          }
          
          // 全てのキーが異なることを確認
          for (let i = 0; i < keys.length; i++) {
            for (let j = i + 1; j < keys.length; j++) {
              expect(keys[i].equals(keys[j])).to.be.false;
            }
          }
          
          // キー長の確認
          keys.forEach(key => {
            expect(key.length).to.equal(32); // 256 bits
          });
        }
      ), { numRuns: 10 });
    });
  });

  describe('暗号化パフォーマンス プロパティテスト', () => {
    
    it('property: 大きなデータサイズでの暗号化性能', () => {
      fc.assert(fc.property(
        fc.integer({ min: 1000, max: 10000 }),
        (dataSize) => {
          const { publicKey, privateKey } = generateRSAKeyPair();
          const largeData = Buffer.alloc(dataSize, 'A');
          
          const startTime = Date.now();
          const { encryptedMessage, encryptedAESKey, iv, tag } = e2eEncrypt(largeData, publicKey);
          const encryptionTime = Date.now() - startTime;
          
          const decryptStartTime = Date.now();
          const decrypted = e2eDecrypt(encryptedMessage, encryptedAESKey, iv, tag, privateKey);
          const decryptionTime = Date.now() - decryptStartTime;
          
          // パフォーマンス要件の確認
          expect(encryptionTime).to.be.lessThan(1000); // 1秒以内
          expect(decryptionTime).to.be.lessThan(500);  // 0.5秒以内
          
          // 正確性の確認
          expect(decrypted.equals(largeData)).to.be.true;
        }
      ), { numRuns: 10 });
    });

    it('property: 暗号化データサイズの線形性', () => {
      fc.assert(fc.property(
        fc.integer({ min: 100, max: 1000 }),
        (baseSize) => {
          const { publicKey } = generateRSAKeyPair();
          
          const data1 = Buffer.alloc(baseSize, 'A');
          const data2 = Buffer.alloc(baseSize * 2, 'B');
          
          const { encryptedMessage: encrypted1 } = e2eEncrypt(data1, publicKey);
          const { encryptedMessage: encrypted2 } = e2eEncrypt(data2, publicKey);
          
          // AES-GCMでは暗号化データサイズは平文サイズと同じ
          expect(encrypted1.length).to.equal(data1.length);
          expect(encrypted2.length).to.equal(data2.length);
          
          // サイズ比の確認
          const ratio = encrypted2.length / encrypted1.length;
          expect(ratio).to.be.approximately(2, 0.1);
        }
      ), { numRuns: 20 });
    });
  });

  describe('エラー条件のプロパティテスト', () => {
    
    it('property: 不正な入力データでの安全な失敗', () => {
      fc.assert(fc.property(
        fc.uint8Array({ minLength: 0, maxLength: 1000 }),
        fc.uint8Array({ minLength: 0, maxLength: 1000 }),
        fc.uint8Array({ minLength: 0, maxLength: 100 }),
        (encryptedData, keyData, ivData) => {
          const { privateKey } = generateRSAKeyPair();
          
          // ランダムなデータで復号を試行
          expect(() => {
            const fakeKey = Buffer.from(keyData);
            const fakeIv = Buffer.from(ivData);
            const fakeTag = crypto.randomBytes(16);
            
            if (fakeKey.length === 32 && fakeIv.length === 16) {
              aesGcmDecrypt(Buffer.from(encryptedData), fakeKey, fakeIv, fakeTag);
            }
          }).to.not.throw.any(['ENOENT', 'EACCES']); // システムエラーは投げない
        }
      ), { numRuns: 50 });
    });
  });
});