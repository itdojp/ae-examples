# E2E暗号化チャットアプリケーション要件仕様書

> **ae-framework準拠** - 6フェーズ開発プロセス対応要件定義

## 1. プロジェクト概要

### 1.1 システム名称
E2E暗号化チャットアプリケーション (Secure Chat System)

### 1.2 目的
エンドツーエンド暗号化により、送信者と受信者以外の第三者（サービス提供者を含む）がメッセージ内容を読めない、高セキュリティのリアルタイムチャットシステムを構築する。

### 1.3 スコープ
- テキストメッセージの暗号化通信
- ユーザー認証とキー管理
- メッセージの完全性検証
- Perfect Forward Secrecy (PFS) の実装
- グループチャット機能（将来拡張）

### 1.4 ae-framework統合要件
本プロジェクトはae-frameworkの6フェーズ開発プロセスに完全対応：

- **Phase 1**: Intent Analysis - 暗号化要件とセキュリティ意図の分析
- **Phase 2**: Natural Language Requirements - 本仕様書の構造化要件処理
- **Phase 3**: User Stories - セキュリティユーザーストーリーとテストケース生成
- **Phase 4**: Validation - セキュリティ要件の多層検証
- **Phase 5**: Domain Modeling - 暗号化ドメインモデルとDDD設計
- **Phase 6**: UI/UX & Frontend - React + Next.js セキュアUI自動生成

### 1.5 開発制約とフレームワーク要件
- **TDD強制**: 全暗号化機能はテストファースト開発
- **形式検証**: Alloy/TLA+によるセキュリティプロパティ検証
- **品質ゲート**: 各フェーズでセキュリティ監査必須
- **テレメトリ**: OpenTelemetryによるセキュリティメトリクス監視

## 2. セキュリティ要件

### 2.1 暗号化要件

#### 2.1.1 暗号化アルゴリズム
- **メッセージ暗号化**: AES-256-GCM
- **鍵交換**: X25519 (Elliptic Curve Diffie-Hellman)
- **デジタル署名**: Ed25519
- **ハッシュ関数**: SHA-256

#### 2.1.2 鍵管理要件
```
要件ID: SEC-001
カテゴリ: 必須
説明: 各ユーザーは以下の鍵ペアを持つ
- 長期身元鍵 (Identity Key Pair)
- 署名済み事前鍵 (Signed Pre-Key)
- 複数の一度限りの事前鍵 (One-Time Pre-Keys)
```

#### 2.1.3 Perfect Forward Secrecy
```
要件ID: SEC-002
カテゴリ: 必須
説明: Double Ratchetアルゴリズムの実装
- メッセージキーは使用後即座に削除
- セッションキーの定期的な再生成
```

### 2.2 認証要件

#### 2.2.1 ユーザー認証
```
要件ID: AUTH-001
カテゴリ: 必須
説明: 多要素認証の実装
- パスワード認証 (最小12文字、複雑性要件あり)
- TOTP/FIDO2による2要素認証
```

#### 2.2.2 デバイス認証
```
要件ID: AUTH-002
カテゴリ: 必須
説明: デバイスフィンガープリンティング
- デバイス固有IDの生成と管理
- 信頼済みデバイスリストの管理
```

### 2.3 データ保護要件

#### 2.3.1 保存データの暗号化
```
要件ID: DATA-001
カテゴリ: 必須
説明: ローカルストレージの暗号化
- SQLCipher or 同等の暗号化DB使用
- デバイス固有の暗号化キー使用
```

#### 2.3.2 メモリ保護
```
要件ID: DATA-002
カテゴリ: 推奨
説明: 機密データのメモリ保護
- 暗号化キーのセキュアメモリ領域での管理
- 使用後の即座のメモリクリア
```

## 3. 機能要件

### 3.1 ユーザー管理

#### 3.1.1 ユーザー登録
```
要件ID: FUNC-001
優先度: 高
説明: 新規ユーザー登録機能
入力: メールアドレス、パスワード、表示名
出力: ユーザーID、初期鍵ペア生成
検証条件: メールアドレスの一意性、パスワード強度
```

#### 3.1.2 ユーザーログイン
```
要件ID: FUNC-002
優先度: 高
説明: 認証とセッション管理
入力: メールアドレス、パスワード、2FA コード
出力: セッショントークン、デバイス登録
検証条件: 認証成功、デバイス信頼性確認
```

### 3.2 メッセージング機能

#### 3.2.1 1対1チャット
```
要件ID: FUNC-003
優先度: 高
説明: 個人間の暗号化メッセージング
機能詳細:
- テキストメッセージの送受信
- 既読確認（任意）
- メッセージの削除（ローカル/双方向）
- タイピングインジケーター（任意）
```

#### 3.2.2 メッセージ同期
```
要件ID: FUNC-004
優先度: 中
説明: マルチデバイス間のメッセージ同期
機能詳細:
- デバイス間の暗号化同期
- オフラインメッセージのキューイング
- 同期状態の表示
```

### 3.3 鍵管理機能

#### 3.3.1 鍵の生成と更新
```
要件ID: FUNC-005
優先度: 高
説明: 暗号鍵のライフサイクル管理
機能詳細:
- 初期鍵ペアの生成
- 事前鍵の定期更新
- 鍵の安全な破棄
```

#### 3.3.2 鍵の検証
```
要件ID: FUNC-006
優先度: 高
説明: 通信相手の身元確認
機能詳細:
- セーフティナンバー/QRコード表示
- 帯域外検証のサポート
- 検証状態の表示
```

## 4. 非機能要件

### 4.1 パフォーマンス要件

```
要件ID: PERF-001
カテゴリ: パフォーマンス
説明: システムレスポンス時間
- メッセージ送信: < 200ms (同一地域内)
- 暗号化処理: < 50ms (1MBまでのメッセージ)
- 鍵交換: < 500ms
```

### 4.2 可用性要件

```
要件ID: AVAIL-001
カテゴリ: 可用性
説明: システム稼働率
- 目標稼働率: 99.9% (年間ダウンタイム < 8.76時間)
- 計画メンテナンス: 月1回、最大2時間
```

### 4.3 スケーラビリティ要件

```
要件ID: SCALE-001
カテゴリ: スケーラビリティ
説明: システム処理能力
- 同時接続ユーザー数: 10,000以上
- メッセージスループット: 1,000 msg/sec
- データベース容量: 水平スケーリング対応
```

## 5. 形式仕様

### 5.1 セキュリティプロパティの形式定義

#### 5.1.1 機密性 (Confidentiality)
```alloy
sig Message {
  sender: User,
  receiver: User,
  content: EncryptedData,
  timestamp: Time
}

sig EncryptedData {
  ciphertext: Data,
  nonce: Nonce,
  tag: AuthTag
}

pred Confidentiality {
  all m: Message |
    m.content.ciphertext != m.content.plaintext and
    canDecrypt[m.receiver, m.content] and
    not canDecrypt[User - m.receiver - m.sender, m.content]
}
```

#### 5.1.2 完全性 (Integrity)
```alloy
pred MessageIntegrity {
  all m: Message |
    verify[m.content.tag, m.content.ciphertext, m.sender.publicKey]
}
```

#### 5.1.3 Perfect Forward Secrecy
```tla+
CONSTANT Users, Keys, Messages
VARIABLE currentKeys, oldKeys, messages

PFS == 
  \A m \in messages:
    \A k \in oldKeys:
      ~CanDecrypt(m, k) /\ 
      (\E k' \in currentKeys: CanDecrypt(m, k'))

KeyRotation ==
  /\ currentKeys' = GenerateNewKeys(Users)
  /\ oldKeys' = oldKeys \cup currentKeys
  /\ UNCHANGED messages
```

### 5.2 プロトコル仕様

#### 5.2.1 Double Ratchetアルゴリズム
```python
class DoubleRatchet:
    def __init__(self):
        self.DHs = None  # DH送信鍵ペア
        self.DHr = None  # DH受信公開鍵
        self.RK = None   # ルート鍵
        self.CKs = None  # 送信チェーン鍵
        self.CKr = None  # 受信チェーン鍵
        
    def ratchet_encrypt(self, plaintext):
        """
        事前条件: self.CKs != None
        事後条件: 新しいメッセージ鍵生成、CKs更新
        """
        message_key = KDF(self.CKs, "MessageKey")
        self.CKs = KDF(self.CKs, "ChainKey")
        
        header = Header(self.DHs.public, self.PN, self.Ns)
        ciphertext = AEAD.encrypt(message_key, plaintext, header)
        
        self.Ns += 1
        return (header, ciphertext)
```

## 6. ae-framework TDD テスト要件

### 6.1 Phase 3: テストファースト開発要件

#### 6.1.1 TDD暗号化テストスイート
```typescript
// 必須テストケース - 実装前に失敗する必要がある (RED phase)
describe('E2EEncryption', () => {
  describe('キー交換プロトコル', () => {
    it('X25519鍵交換が正常に完了する', async () => {
      // Given: 2つのクライアント
      const alice = new SecureChatClient('alice');
      const bob = new SecureChatClient('bob');
      
      // When: 鍵交換を実行
      const session = await alice.initiateKeyExchange(bob.getPublicKey());
      
      // Then: 共有秘密鍵が生成される
      expect(session.sharedSecret).toBeDefined();
      expect(session.sharedSecret).toHaveLength(32); // 256 bits
    });

    it('Double Ratchet初期化が成功する', async () => {
      const session = await createTestSession();
      expect(session.rootKey).toBeDefined();
      expect(session.chainKeySend).toBeDefined();
      expect(session.chainKeyReceive).toBeDefined();
    });
  });

  describe('メッセージ暗号化', () => {
    it('AES-256-GCMでメッセージを暗号化する', async () => {
      const plaintext = 'Hello, secure world!';
      const encrypted = await encryptMessage(plaintext, testKey);
      
      expect(encrypted.ciphertext).not.toBe(plaintext);
      expect(encrypted.nonce).toHaveLength(12);
      expect(encrypted.authTag).toHaveLength(16);
    });

    it('暗号化されたメッセージの復号が成功する', async () => {
      const plaintext = 'Test message';
      const encrypted = await encryptMessage(plaintext, testKey);
      const decrypted = await decryptMessage(encrypted, testKey);
      
      expect(decrypted).toBe(plaintext);
    });

    it('無効な認証タグで復号が失敗する', async () => {
      const plaintext = 'Test message';
      const encrypted = await encryptMessage(plaintext, testKey);
      encrypted.authTag = Buffer.from('invalid-tag-data');
      
      await expect(decryptMessage(encrypted, testKey))
        .rejects.toThrow('Authentication failed');
    });
  });

  describe('Perfect Forward Secrecy', () => {
    it('メッセージキーが使用後に削除される', async () => {
      const session = await createTestSession();
      const messageKey = await session.getNextMessageKey();
      
      await session.encryptMessage('test', messageKey);
      
      // メッセージキーが削除されているはず
      expect(() => session.getStoredMessageKey(messageKey.id))
        .toThrow('Message key not found');
    });

    it('古いメッセージキーで新しいメッセージを復号できない', async () => {
      const session = await createTestSession();
      const oldKey = await session.getNextMessageKey();
      
      // キーローテーション実行
      await session.rotateKeys();
      
      const newMessage = 'This is a new message';
      await expect(session.encryptMessage(newMessage, oldKey))
        .rejects.toThrow('Key rotation detected');
    });
  });
});
```

### 6.2 Phase 4: セキュリティ検証テスト (GREEN phase実装後)

#### 6.2.1 暗号化プロパティテスト
```typescript
import fc from 'fast-check';

describe('暗号化プロパティテスト', () => {
  it('任意のメッセージが暗号化・復号で元に戻る', () => {
    fc.assert(fc.property(
      fc.string({ minLength: 1, maxLength: 10000 }),
      async (message) => {
        const key = await generateSecureKey();
        const encrypted = await encryptMessage(message, key);
        const decrypted = await decryptMessage(encrypted, key);
        
        expect(decrypted).toBe(message);
      }
    ));
  });

  it('異なる鍵で暗号化したメッセージは復号できない', () => {
    fc.assert(fc.property(
      fc.string({ minLength: 1 }),
      async (message) => {
        const key1 = await generateSecureKey();
        const key2 = await generateSecureKey();
        
        const encrypted = await encryptMessage(message, key1);
        
        await expect(decryptMessage(encrypted, key2))
          .rejects.toThrow();
      }
    ));
  });
});
```

### 6.3 BDD セキュリティシナリオ

#### 6.3.1 Gherkin暗号化シナリオ
```gherkin
# features/e2e-encryption.feature
Feature: End-to-End Encryption
  As a security-conscious user
  I want my messages to be encrypted end-to-end
  So that only the intended recipient can read them

  Background:
    Given Alice and Bob are registered users
    And they have completed device verification
    
  Scenario: Successful encrypted message exchange
    Given Alice initiates a chat with Bob
    When Alice sends "Hello Bob!" to Bob
    Then Bob receives the encrypted message
    And Bob can decrypt and read "Hello Bob!"
    And no intermediary can read the message content

  Scenario: Perfect Forward Secrecy protection
    Given Alice and Bob have exchanged multiple messages
    And their session keys have rotated
    When an attacker compromises the current session key
    Then the attacker cannot decrypt previous messages
    And the attacker cannot decrypt future messages

  Scenario: Device verification prevents MITM attacks
    Given Alice attempts to chat with Bob
    And there is a man-in-the-middle attack
    When Alice checks Bob's safety number
    Then Alice sees a security warning
    And the connection is not trusted until verification
```

### 6.4 セキュリティテスト

#### 6.1.1 暗号化テスト
```
テストID: TEST-SEC-001
目的: E2E暗号化の正常性確認
手順:
1. 2つのクライアント間でセッション確立
2. メッセージ送信と暗号化確認
3. ネットワーク上のパケットキャプチャ
4. 暗号文の解読不可能性確認
期待結果: 暗号文から平文を復元できない
```

#### 6.1.2 鍵漏洩テスト
```
テストID: TEST-SEC-002
目的: PFSの動作確認
手順:
1. 複数のメッセージ交換
2. 現在のセッション鍵を意図的に漏洩
3. 過去のメッセージの復号試行
期待結果: 過去のメッセージは復号できない
```

### 6.2 機能テスト

#### 6.2.1 メッセージ送受信テスト
```
テストID: TEST-FUNC-001
目的: 基本的なメッセージング機能の確認
テストケース:
- 正常系: メッセージ送受信成功
- 異常系: ネットワーク切断時の再送
- 境界値: 最大メッセージサイズ (10MB)
```

### 6.3 負荷テスト

```
テストID: TEST-LOAD-001
目的: システムの負荷耐性確認
条件:
- 同時接続: 1,000ユーザー
- メッセージレート: 100 msg/sec/user
- 継続時間: 1時間
評価基準:
- CPU使用率 < 80%
- メモリ使用率 < 70%
- レスポンス時間 < 500ms (95パーセンタイル)
```

## 7. 制約事項

### 7.1 技術的制約
- 暗号化ライブラリ: libsodium or OpenSSL (FIPS 140-2認証版)
- プラットフォーム: iOS 14+, Android 10+, Web (Chrome/Firefox最新版)
- プロトコル: WebSocket over TLS 1.3

### 7.2 法的制約
- GDPR準拠（EU居住者のデータ保護）
- 各国の暗号化規制への準拠
- データローカライゼーション要件の考慮

## 8. リスク分析

### 8.1 セキュリティリスク

| リスクID | リスク内容 | 影響度 | 発生確率 | 対策 |
|---------|-----------|--------|----------|------|
| RISK-001 | 中間者攻撃 | 高 | 中 | 証明書ピンニング、鍵検証機能 |
| RISK-002 | 鍵の漏洩 | 高 | 低 | HSM使用、定期的な鍵更新 |
| RISK-003 | サイドチャネル攻撃 | 中 | 低 | 定時間アルゴリズム実装 |
| RISK-004 | メタデータ漏洩 | 中 | 中 | メタデータの最小化、Torサポート |

### 8.2 運用リスク

| リスクID | リスク内容 | 影響度 | 発生確率 | 対策 |
|---------|-----------|--------|----------|------|
| RISK-005 | スケーリング問題 | 中 | 中 | 自動スケーリング、負荷分散 |
| RISK-006 | データ損失 | 高 | 低 | 定期バックアップ、レプリケーション |

## 9. 受け入れ基準

### 9.1 セキュリティ基準
- [ ] 全ての暗号化要件を満たしている
- [ ] セキュリティ監査に合格
- [ ] ペネトレーションテストで重大な脆弱性なし

### 9.2 機能基準
- [ ] 全ての必須機能要件を実装
- [ ] ユーザビリティテストで80%以上の満足度

### 9.3 パフォーマンス基準
- [ ] 定義されたレスポンス時間を満たす
- [ ] 負荷テストに合格

## 10. Phase 5: 暗号化ドメインモデリング (DDD)

### 10.1 暗号化ドメインエンティティ

#### 10.1.1 コアドメインエンティティ
```typescript
// Domain Entity: User (ユーザー集約ルート)
export class User {
  constructor(
    private readonly userId: UserId,
    private readonly identityKeyPair: IdentityKeyPair,
    private readonly signedPreKey: SignedPreKey,
    private oneTimePreKeys: OneTimePreKey[]
  ) {}

  public rotateSignedPreKey(): SignedPreKey {
    // ビジネスルール: 署名済み事前鍵は7日で更新
    if (!this.signedPreKey.needsRotation()) {
      throw new DomainError('Signed pre-key rotation not due');
    }
    return SignedPreKey.generate(this.identityKeyPair);
  }

  public consumeOneTimePreKey(): OneTimePreKey | null {
    // ビジネスルール: 一度限り事前鍵は使用後削除
    return this.oneTimePreKeys.shift() || null;
  }
}

// Domain Entity: SecureSession (セッション集約)
export class SecureSession {
  constructor(
    private readonly sessionId: SessionId,
    private readonly participants: [UserId, UserId],
    private ratchetState: DoubleRatchetState
  ) {}

  public encryptMessage(plaintext: string): EncryptedMessage {
    // ビジネスルール: Perfect Forward Secrecy
    const messageKey = this.ratchetState.deriveMessageKey();
    const encrypted = AES_GCM.encrypt(plaintext, messageKey);
    
    // メッセージキー即座削除
    messageKey.destroy();
    
    return new EncryptedMessage(encrypted, this.sessionId);
  }

  public rotateKeys(): void {
    // ビジネスルール: 定期的なキーローテーション
    this.ratchetState = this.ratchetState.performDHRatchet();
  }
}

// Value Object: CryptographicKey
export class CryptographicKey {
  constructor(
    private readonly keyData: Uint8Array,
    private readonly algorithm: CryptoAlgorithm,
    private readonly createdAt: Date
  ) {
    if (keyData.length !== this.expectedKeyLength()) {
      throw new DomainError(`Invalid key length for ${algorithm}`);
    }
  }

  public destroy(): void {
    // メモリセキュリティ: キーデータのゼロクリア
    this.keyData.fill(0);
  }

  private expectedKeyLength(): number {
    switch (this.algorithm) {
      case 'AES-256': return 32;
      case 'X25519': return 32;
      case 'Ed25519': return 32;
      default: throw new DomainError(`Unknown algorithm: ${this.algorithm}`);
    }
  }
}
```

#### 10.1.2 境界コンテキスト定義
```typescript
// Bounded Context: Cryptography
export interface CryptographyService {
  generateKeyPair(algorithm: KeyAlgorithm): KeyPair;
  encrypt(plaintext: string, key: CryptographicKey): EncryptedData;
  decrypt(ciphertext: EncryptedData, key: CryptographicKey): string;
  performKeyExchange(ourPrivate: PrivateKey, theirPublic: PublicKey): SharedSecret;
}

// Bounded Context: Session Management  
export interface SessionRepository {
  findById(sessionId: SessionId): SecureSession | null;
  save(session: SecureSession): void;
  removeExpiredSessions(): void;
}

// Bounded Context: User Management
export interface UserRepository {
  findById(userId: UserId): User | null;
  save(user: User): void;
  findByPublicKey(publicKey: PublicKey): User | null;
}
```

### 10.2 ドメインサービス

#### 10.2.1 セッション開始サービス
```typescript
export class SessionInitiationService {
  constructor(
    private readonly userRepo: UserRepository,
    private readonly sessionRepo: SessionRepository,
    private readonly cryptoService: CryptographyService
  ) {}

  public async initiateSession(
    initiatorId: UserId, 
    recipientId: UserId
  ): Promise<SecureSession> {
    const initiator = await this.userRepo.findById(initiatorId);
    const recipient = await this.userRepo.findById(recipientId);
    
    if (!initiator || !recipient) {
      throw new DomainError('User not found');
    }

    // Signal Protocol鍵交換の実装
    const oneTimeKey = recipient.consumeOneTimePreKey();
    if (!oneTimeKey) {
      throw new DomainError('No one-time pre-keys available');
    }

    const sharedSecret = this.cryptoService.performKeyExchange(
      initiator.getIdentityKeyPair().privateKey,
      recipient.getSignedPreKey().publicKey
    );

    const session = new SecureSession(
      SessionId.generate(),
      [initiatorId, recipientId],
      DoubleRatchetState.initialize(sharedSecret)
    );

    await this.sessionRepo.save(session);
    return session;
  }
}
```

## 11. Phase 6: セキュアUI/UX自動生成要件

### 11.1 React セキュアコンポーネント生成

#### 11.1.1 セキュリティ強化UIコンポーネント
```typescript
// 自動生成対象: SecureChatInterface
interface SecureChatProps {
  currentUser: User;
  session: SecureSession;
  onSendMessage: (message: string) => Promise<void>;
}

export const SecureChatInterface: React.FC<SecureChatProps> = ({
  currentUser,
  session,
  onSendMessage
}) => {
  const [message, setMessage] = useState('');
  const [encryptionStatus, setEncryptionStatus] = useState<'secure' | 'warning' | 'error'>('secure');

  // セキュリティ表示ロジック
  const getSecurityIcon = () => {
    switch (encryptionStatus) {
      case 'secure': return <ShieldCheckIcon className="text-green-500" />;
      case 'warning': return <ShieldExclamationIcon className="text-yellow-500" />;
      case 'error': return <ShieldXIcon className="text-red-500" />;
    }
  };

  const handleSend = async () => {
    if (!message.trim()) return;
    
    try {
      await onSendMessage(message);
      setMessage('');
    } catch (error) {
      setEncryptionStatus('error');
      // エラーハンドリング
    }
  };

  return (
    <div className="flex flex-col h-full bg-gray-50" role="main" aria-label="Secure Chat Interface">
      {/* セキュリティステータスバー */}
      <div className="bg-green-100 p-2 border-b flex items-center justify-center">
        {getSecurityIcon()}
        <span className="ml-2 text-sm font-medium">
          End-to-End Encrypted with {session.getRecipient().displayName}
        </span>
      </div>

      {/* メッセージ履歴 */}
      <MessageHistory 
        session={session}
        className="flex-1 overflow-y-auto"
        aria-label="Message History"
      />

      {/* セキュアメッセージ入力フォーム */}
      <form onSubmit={handleSend} className="p-4 border-t bg-white">
        <div className="flex gap-2">
          <Input
            value={message}
            onChange={(e) => setMessage(e.target.value)}
            placeholder="Type a secure message..."
            className="flex-1"
            aria-label="Message input"
            autoComplete="off"
            data-lpignore="true"  // パスワードマネージャー対策
          />
          <Button 
            type="submit" 
            disabled={!message.trim()}
            className="bg-blue-600 hover:bg-blue-700"
            aria-label="Send encrypted message"
          >
            <SendIcon className="w-4 h-4" />
          </Button>
        </div>
      </form>
    </div>
  );
};
```

#### 11.1.2 セキュリティ検証UIコンポーネント
```typescript
// 自動生成対象: SafetyNumberVerification
export const SafetyNumberVerification: React.FC<{
  localFingerprint: string;
  remoteFingerprint: string;
  onVerificationComplete: (verified: boolean) => void;
}> = ({ localFingerprint, remoteFingerprint, onVerificationComplete }) => {
  const [manualVerification, setManualVerification] = useState(false);

  return (
    <Dialog>
      <DialogContent className="max-w-md">
        <DialogHeader>
          <DialogTitle className="flex items-center gap-2">
            <ShieldCheckIcon className="w-5 h-5" />
            Verify Identity
          </DialogTitle>
        </DialogHeader>

        <div className="space-y-4">
          <div>
            <label className="text-sm font-medium">Your Safety Number</label>
            <div className="font-mono text-sm bg-gray-100 p-2 rounded">
              {formatSafetyNumber(localFingerprint)}
            </div>
          </div>

          <div>
            <label className="text-sm font-medium">Contact's Safety Number</label>
            <div className="font-mono text-sm bg-gray-100 p-2 rounded">
              {formatSafetyNumber(remoteFingerprint)}
            </div>
          </div>

          <div className="flex items-center space-x-2">
            <Checkbox 
              id="manual-verify"
              checked={manualVerification}
              onCheckedChange={setManualVerification}
            />
            <label htmlFor="manual-verify" className="text-sm">
              I have verified these numbers match through a secure channel
            </label>
          </div>

          <div className="flex gap-2">
            <Button 
              variant="outline" 
              onClick={() => onVerificationComplete(false)}
            >
              Cancel
            </Button>
            <Button 
              onClick={() => onVerificationComplete(manualVerification)}
              disabled={!manualVerification}
              className="bg-green-600 hover:bg-green-700"
            >
              Verify Identity
            </Button>
          </div>
        </div>
      </DialogContent>
    </Dialog>
  );
};
```

### 11.2 セキュリティテレメトリ統合

#### 11.2.1 OpenTelemetryセキュリティメトリクス
```typescript
// 自動監視メトリクス
export class SecurityTelemetryCollector {
  private meter = metrics.getMeter('secure-chat', '1.0.0');
  
  // セキュリティメトリクス定義
  private encryptionLatency = this.meter.createHistogram('encryption_duration_ms', {
    description: 'Time taken to encrypt a message',
    unit: 'ms'
  });

  private keyRotationCounter = this.meter.createCounter('key_rotations_total', {
    description: 'Total number of key rotations'
  });

  private authFailures = this.meter.createCounter('authentication_failures_total', {
    description: 'Total authentication failures'
  });

  public recordEncryption(durationMs: number, messageSize: number): void {
    this.encryptionLatency.record(durationMs, {
      'message.size_category': this.getSizeCategory(messageSize)
    });
  }

  public recordKeyRotation(sessionId: string): void {
    this.keyRotationCounter.add(1, {
      'session.id': sessionId
    });
  }

  public recordAuthFailure(reason: string): void {
    this.authFailures.add(1, {
      'failure.reason': reason
    });
  }
}
```

### 11.3 アクセシビリティ・セキュリティ統合

#### 11.3.1 セキュアアクセシビリティ要件
```typescript
// WCAG 2.1 AA + セキュリティ準拠
export const SecureAccessibilityRequirements = {
  // スクリーンリーダー対応
  ariaLabels: {
    encryptionStatus: 'Message encryption status',
    safetyNumber: 'Identity verification safety number',
    messageInput: 'Encrypted message composition area'
  },

  // キーボードナビゲーション
  keyboardShortcuts: {
    'Ctrl+E': 'Verify contact identity',
    'Ctrl+Shift+D': 'Delete message history',
    'Ctrl+L': 'Lock application'
  },

  // 高コントラスト対応
  colorScheme: {
    secure: { bg: '#10b981', text: '#ffffff' },      // Green
    warning: { bg: '#f59e0b', text: '#000000' },     // Yellow  
    error: { bg: '#ef4444', text: '#ffffff' }        // Red
  },

  // セキュリティアラート
  announcements: {
    keyRotation: 'Security keys have been updated',
    verificationRequired: 'Contact verification required for secure communication',
    encryptionEnabled: 'End-to-end encryption is active'
  }
};
```

## 12. 付録

### 10.1 用語集
- **E2E暗号化**: エンドツーエンド暗号化。送信者と受信者のみがメッセージを復号できる暗号化方式
- **Double Ratchet**: Signal Protocolで使用される暗号化アルゴリズム
- **PFS**: Perfect Forward Secrecy。過去の通信の秘密性を保証する性質
- **HSM**: Hardware Security Module。暗号鍵を安全に管理するハードウェア

### 10.2 参考文献
- Signal Protocol Specification
- NIST SP 800-57: Recommendation for Key Management
- RFC 7748: Elliptic Curves for Security
- OWASP Mobile Security Testing Guide

## 13. ae-framework開発ワークフロー指示

### 13.1 Claude Code Task Tool統合での開発手順

#### 13.1.1 Phase 1: Intent Analysis実行
```bash
# Claude Code環境での実行例
User: この暗号化チャットアプリの要件を分析してください

Claude Code: Intent Task Adapterを実行して要件分析を行います...

✅ Intent Analysis Complete - 25 security requirements identified
📊 分析結果:
  • 暗号化要件: 8項目
  • 認証要件: 5項目  
  • セキュリティ要件: 7項目
  • UI/UX要件: 3項目
  • 非機能要件: 2項目
💡 推奨事項:
  • Signal Protocolの完全実装が必要
  • Perfect Forward Secrecyの実装優先度高
  • OWASP Mobile Security準拠が必要
```

#### 13.1.2 Phase 2-6: 完全自動化実行
```bash
# Phase 2: Natural Language Requirements
User: 要件を構造化してください
Claude Code: Natural Language Task Adapterで処理中...
✅ Requirements Analysis Complete - 25 structured requirements

# Phase 3: User Stories & TDD Tests  
User: セキュリティユーザーストーリーを作成してください
Claude Code: User Stories Task Adapterで処理中...
✅ Security User Stories Complete - 12 stories, 8 security epics
🧪 TDD Test Suite Generated - 45 failing tests ready for implementation

# Phase 4: Cross-Validation
User: セキュリティ要件の整合性を検証してください  
Claude Code: Validation Task Adapterで検証中...
✅ Security Requirements Validation - 98% alignment, OWASP compliant

# Phase 5: Domain Modeling
User: 暗号化ドメインモデルを設計してください
Claude Code: Domain Modeling Task Adapterで設計中...
✅ Cryptographic Domain Model Complete - 6 entities, 3 bounded contexts

# Phase 6: Secure UI Generation
User: セキュアなチャットUIを生成してください
Claude Code: UI Task Adapterでコンポーネント生成中...

📊 OpenTelemetry initialized for secure-chat Phase 6
   Service: ae-framework-secure-chat v1.0.0
   Environment: development
   Security Level: High (E2E Encryption)

✅ Generated 28 secure UI files
📊 Security Compliance: 100% ✅
🛡️ Encryption Integration: ✅ Complete
♿ A11y Score: 98% (WCAG 2.1 AA) ✅
🔐 Security Test Coverage: 95% ✅
```

### 13.2 CLI実行による開発管理

#### 13.2.1 プロジェクト初期化
```bash
# ae-frameworkプロジェクト初期化
ae-framework init secure-chat --tdd --security=high

# Steering Documents作成
mkdir -p .ae/steering
cat > .ae/steering/product.md << 'EOF'
# Secure Chat Product Vision

## Mission
Build the most secure, user-friendly E2E encrypted chat application

## Target Users  
- Privacy-conscious individuals
- Journalists and activists
- Healthcare professionals
- Business executives

## Core Security Features
- Signal Protocol implementation
- Perfect Forward Secrecy
- Device verification
- Metadata protection
EOF

cat > .ae/steering/architecture.md << 'EOF'
# Secure Chat Architecture

## Technology Stack
- Backend: Node.js + Fastify + PostgreSQL
- Crypto: libsodium (WebCrypto API fallback)
- Frontend: Next.js 14 + React 18 + Tailwind CSS
- E2E Testing: Playwright + Security test suite
- Monitoring: OpenTelemetry + Security metrics

## Security Architecture
- Zero-knowledge server design
- Client-side encryption only
- Ephemeral message keys
- Forward secure key derivation
EOF
```

#### 13.2.2 フェーズ実行とテスト
```bash
# TDDテスト生成とRED phase確認
ae-framework generate:tests --feature="E2E Encryption"
npm test  # 失敗することを確認 (RED)

# 暗号化実装生成 
ae-framework generate:code --tdd
npm test  # 成功することを確認 (GREEN)

# セキュリティ検証実行
ae-framework verify --security
# - 暗号化強度テスト
# - タイミング攻撃耐性テスト  
# - メモリリーク検査
# - OWASP Mobile Top 10チェック

# セキュアUI生成
ae-framework ui-scaffold --security --components
# - 暗号化ステータス表示
# - セーフティナンバー検証UI
# - セキュアメッセージ入力フォーム
# - A11y準拠のセキュリティ警告
```

### 13.3 品質ゲートとセキュリティ監査

#### 13.3.1 必須セキュリティ品質ゲート
```yaml
# .ae/gates/security.yaml
security_gates:
  phase_3_tests:
    - name: "暗号化テストカバレッジ"
      threshold: 95%
      type: coverage
    - name: "セキュリティテスト実行"  
      command: "npm run test:security"
      expect: all_pass
      
  phase_4_implementation:
    - name: "暗号化アルゴリズム検証"
      validator: "crypto_algorithm_validator"
      algorithms: ["AES-256-GCM", "X25519", "Ed25519"]
    - name: "タイミング攻撃耐性"
      command: "npm run test:timing-attacks"
      
  phase_5_verification:
    - name: "OWASP Mobile Top 10"
      command: "npm run security:owasp-mobile"
    - name: "暗号化メモリ保護"
      command: "npm run test:memory-protection"
      
  phase_6_ui:
    - name: "セキュアUI監査"
      command: "npm run test:secure-ui"
    - name: "A11y+セキュリティ統合"
      threshold: 95%
      type: a11y_security
```

#### 13.3.2 OpenTelemetryセキュリティ監視
```bash
# セキュリティテレメトリ有効化
DEBUG_TELEMETRY=true SECURITY_MONITORING=enabled ae-framework ui-scaffold --security

# 監視対象メトリクス
# - 暗号化処理時間 (≤50ms)
# - 鍵ローテーション頻度 (7日間隔)
# - 認証失敗率 (≤1%)
# - メモリリーク検出 (0件)
# - セキュリティ警告表示率 (100%)
```

### 13.4 継続的セキュリティ統合 (CI/CD)

#### 13.4.1 GitHub Actions統合例
```yaml
# .github/workflows/security-validation.yml
name: Security Validation Pipeline

on: [push, pull_request]

jobs:
  security_audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Setup ae-framework
        run: |
          npm install
          npm run build
          
      - name: Phase 3 Security Tests (RED/GREEN)
        run: |
          ae-framework generate:tests --security
          npm test -- --testNamePattern="Security|Encryption"
          
      - name: Phase 4 Crypto Implementation Validation
        run: |
          ae-framework verify --cryptography
          npm run test:timing-attacks
          
      - name: Phase 5 OWASP Mobile Security Check
        run: |
          npm run security:owasp-mobile
          npm run test:penetration
          
      - name: Phase 6 Secure UI/UX Validation
        run: |
          ae-framework ui-scaffold --security --validate-only
          npm run test:secure-ui
          npm run test:a11y:security
```

### 13.5 開発完了チェックリスト

#### 13.5.1 各フェーズ完了基準
```markdown
## Phase 1: Intent Analysis ✅
- [ ] セキュリティ要件25項目特定完了
- [ ] Signal Protocol準拠確認
- [ ] OWASP Mobile Security準拠計画確認

## Phase 2: Natural Language Requirements ✅  
- [ ] 構造化要件25項目完了
- [ ] セキュリティ用語辞書作成完了
- [ ] 暗号化仕様明確化完了

## Phase 3: User Stories & TDD ✅
- [ ] セキュリティユーザーストーリー12件完了
- [ ] TDDテストスイート45件実装完了  
- [ ] 全テスト初期実行で失敗確認 (RED phase)

## Phase 4: Cross-Validation ✅
- [ ] セキュリティ要件整合性98%以上
- [ ] 暗号化アルゴリズム検証完了
- [ ] OWASP準拠100%確認

## Phase 5: Domain Modeling ✅
- [ ] 暗号化ドメインモデル完了 (6エンティティ)
- [ ] 境界コンテキスト設計完了 (3コンテキスト)  
- [ ] セキュリティビジネスルール実装完了

## Phase 6: Secure UI/UX ✅
- [ ] セキュアUIコンポーネント28件生成完了
- [ ] A11y準拠98%以上達成
- [ ] セキュリティテレメトリ統合完了
- [ ] OpenTelemetryセキュリティメトリクス監視開始
```

### 10.3 改訂履歴
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2025-08-08 | 初版作成 | System |
| 2.0 | 2025-08-18 | ae-framework統合、6フェーズ対応、TDD/DDD/UI自動生成要件追加 | ae-framework |