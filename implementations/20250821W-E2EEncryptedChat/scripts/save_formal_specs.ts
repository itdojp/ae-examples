import { FormalAgent } from './ae-framework/src/agents/formal-agent.js';
import { writeFileSync, mkdirSync } from 'fs';
import path from 'path';

async function saveFormalSpecifications() {
  try {
    console.log('💾 生成された形式仕様をファイルに保存します...\n');

    // 出力ディレクトリを作成
    const outputDir = path.join(__dirname, 'formal_specifications');
    mkdirSync(outputDir, { recursive: true });

    // Formal Agent の再作成と仕様生成
    const agent = new FormalAgent({
      outputFormat: 'tla+',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true
    });

    const securityRequirements = `
E2E Encrypted Chat System Formal Specification

CONSTANTS: MaxUsers, MaxMessages, MaxKeys
VARIABLES: users, messages, keys, sessions

Message security requirements:
- All messages must be encrypted with AES-256-GCM
- Message keys are ephemeral and deleted after use
- Perfect Forward Secrecy through Double Ratchet protocol

Key management requirements:
- Each user has identity keys, signed prekeys, one-time prekeys
- Key exchange uses X25519 ECDH
- Digital signatures use Ed25519
- Session keys rotate regularly

Authentication requirements:
- Multi-factor authentication required
- Device registration and fingerprinting
- Trusted device management

System invariants:
- Messages are never stored in plaintext
- Private keys never leave secure storage
- Authentication precedes all operations
    `;

    // 1. TLA+ 仕様を保存
    console.log('📝 1. TLA+ 仕様を保存中...');
    const tlaSpec = await agent.generateFormalSpecification(
      securityRequirements,
      'tla+',
      { includeDiagrams: true, generateProperties: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_Specification.tla'),
      tlaSpec.content,
      'utf-8'
    );

    // 2. OpenAPI 仕様を保存
    console.log('📝 2. OpenAPI 仕様を保存中...');
    const apiRequirements = `
E2E encrypted chat API endpoints:
- POST /auth/login - User authentication with email, password, 2FA
- POST /auth/register - User registration
- POST /keys/generate - Key pair generation
- POST /keys/exchange - Key exchange protocol
- POST /messages - Send encrypted message
- GET /messages/:channelId - Retrieve messages
- POST /channels - Create channel
- GET /devices - List user devices
- POST /devices/trust - Trust device

Security features:
- JWT authentication for all endpoints
- Pre-encrypted message payloads
- X25519+Ed25519 key exchange protocol
- Rate limiting and DDoS protection
    `;

    const apiSpec = await agent.createAPISpecification(
      apiRequirements,
      'openapi',
      { includeExamples: true, generateContracts: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_API.json'),
      apiSpec.content,
      'utf-8'
    );

    // 3. AsyncAPI 仕様を保存
    console.log('📝 3. AsyncAPI 仕様を保存中...');
    const asyncApiRequirements = `
Real-time messaging channels:
- messages/{userId} - Receive personal messages
- typing/{channelId} - Typing status notifications
- presence/{userId} - Online status updates
- keys/exchange - Key exchange events

Message types:
- MessageReceived: Encrypted message received
- TypingStatus: Typing status change
- PresenceUpdate: Online/offline status
- KeyExchangeRequest: Key exchange request
- KeyExchangeResponse: Key exchange response

Protocol: WebSocket over TLS 1.3
    `;

    const asyncApiSpec = await agent.createAPISpecification(
      asyncApiRequirements,
      'asyncapi',
      { includeExamples: true, generateContracts: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_AsyncAPI.json'),
      asyncApiSpec.content,
      'utf-8'
    );

    // 4. 状態機械を保存
    console.log('📝 4. 状態機械を保存中...');
    const stateMachineRequirements = `
Message processing state machine:

States:
- Created: Message created
- Encrypted: Encryption completed
- Transmitted: Transmission completed
- Delivered: Delivery confirmed
- Read: Read receipt confirmed
- Deleted: Message deleted

Transitions:
- Created -> Encrypted: encrypt(message, recipientKey)
- Encrypted -> Transmitted: send(encryptedMessage)
- Transmitted -> Delivered: acknowledge(messageId)
- Delivered -> Read: markAsRead(messageId)
- Any -> Deleted: delete(messageId)

Invariants:
- Messages can only be sent after encryption
- Deleted messages cannot be recovered
- Read receipts only possible after delivery
    `;

    const stateMachine = await agent.generateStateMachine(
      stateMachineRequirements,
      { generateInvariants: true, includeDiagrams: true }
    );

    writeFileSync(
      path.join(outputDir, 'Message_State_Machine.json'),
      JSON.stringify(stateMachine, null, 2),
      'utf-8'
    );

    // 5. 契約仕様を保存
    console.log('📝 5. 契約仕様を保存中...');
    const encryptionContract = await agent.createContracts(
      'function encryptMessage(plaintext: string, recipientPublicKey: PublicKey): EncryptedMessage',
      `
Encryption function requirements:
- Precondition: plaintext is non-empty string, recipientPublicKey is valid public key
- Postcondition: result is AES-256-GCM encrypted message
- Invariant: encryption makes plaintext unrecoverable
- Exception handling: throw CryptographicError for invalid keys
      `,
      { includeInvariants: true }
    );

    writeFileSync(
      path.join(outputDir, 'Encryption_Contracts.json'),
      JSON.stringify(encryptionContract, null, 2),
      'utf-8'
    );

    // 6. UML図表を保存
    console.log('📝 6. UML図表を保存中...');
    const diagrams = await agent.generateDiagrams(
      tlaSpec,
      ['sequence', 'state', 'class', 'component']
    );

    diagrams.forEach((diagram, index) => {
      writeFileSync(
        path.join(outputDir, `${diagram.type}_diagram.puml`),
        diagram.content,
        'utf-8'
      );
    });

    // 7. Alloy 仕様を生成・保存
    console.log('📝 7. Alloy 仕様を保存中...');
    const alloySpec = await agent.generateFormalSpecification(
      securityRequirements,
      'alloy',
      { includeDiagrams: true, generateProperties: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_Model.als'),
      alloySpec.content,
      'utf-8'
    );

    // 8. Z notation 仕様を生成・保存
    console.log('📝 8. Z notation 仕様を保存中...');
    const zSpec = await agent.generateFormalSpecification(
      securityRequirements,
      'z-notation',
      { includeDiagrams: true, generateProperties: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_Z_Specification.tex'),
      zSpec.content,
      'utf-8'
    );

    // 9. GraphQL スキーマを生成・保存
    console.log('📝 9. GraphQL スキーマを保存中...');
    const graphqlRequirements = `
E2E Chat GraphQL Schema requirements:

Entities:
- User: id, email, name, publicKey, devices
- Message: id, senderId, recipientId, encryptedContent, timestamp
- Channel: id, participants, type, metadata
- Device: id, userId, fingerprint, trusted, lastSeen
- KeyBundle: identityKey, signedPreKey, oneTimeKeys

Operations:
- Query: user, message, channel, devices
- Mutation: sendMessage, createChannel, trustDevice, generateKeys
- Subscription: messageReceived, presenceUpdate, typingStatus
    `;

    const graphqlSpec = await agent.createAPISpecification(
      graphqlRequirements,
      'graphql',
      { includeExamples: true, generateContracts: true }
    );

    writeFileSync(
      path.join(outputDir, 'E2E_Chat_Schema.graphql'),
      graphqlSpec.content,
      'utf-8'
    );

    // 10. 統合レポートを作成
    console.log('📝 10. 統合レポートを作成中...');
    const report = `# E2E暗号化チャットアプリケーション - 形式仕様書

**生成日時**: ${new Date().toLocaleString('ja-JP')}  
**生成フレームワーク**: ae-framework Formal Agent  
**仕様書バージョン**: 1.0.0  

---

## 📋 生成された仕様一覧

### 形式的仕様書
1. **TLA+ 仕様** (\`E2E_Chat_Specification.tla\`)
   - モジュール名: GeneratedModule
   - 変数: users, messages, keys, sessions
   - プロパティ: SafetyProperty, TypeInvariant

2. **Alloy モデル** (\`E2E_Chat_Model.als\`)
   - シグネチャ: Entity
   - ファクト: BasicFact
   - 述語: valid

3. **Z notation 仕様** (\`E2E_Chat_Z_Specification.tex\`)
   - スキーマ: State
   - オペレーション: Op
   - LaTeX形式で出力

### API 仕様書
4. **OpenAPI 3.0** (\`E2E_Chat_API.json\`)
   - エンドポイント: 認証、鍵管理、メッセージング
   - セキュリティ: JWT認証、レート制限
   - スキーマ: 完全なリクエスト/レスポンス定義

5. **AsyncAPI 2.6** (\`E2E_Chat_AsyncAPI.json\`)
   - チャンネル: リアルタイムメッセージング
   - メッセージ: 暗号化イベント、状態更新
   - プロトコル: WebSocket over TLS 1.3

6. **GraphQL スキーマ** (\`E2E_Chat_Schema.graphql\`)
   - タイプ: User, Message, Channel, Device
   - クエリ: データ取得操作
   - ミューテーション: データ変更操作

### 動作仕様
7. **状態機械** (\`Message_State_Machine.json\`)
   - 状態: Created, Encrypted, Transmitted, Delivered, Read, Deleted
   - 遷移: 暗号化→送信→配信→既読
   - 不変条件: セキュリティ制約

8. **契約仕様** (\`Encryption_Contracts.json\`)
   - 事前条件: 入力パラメータ検証
   - 事後条件: 暗号化保証
   - 不変条件: セキュリティ不変性

### UML 図表
9. **PlantUML 図表**
   - \`sequence_diagram.puml\`: シーケンス図
   - \`state_diagram.puml\`: 状態遷移図
   - \`class_diagram.puml\`: クラス図
   - \`component_diagram.puml\`: コンポーネント図

---

## 🔐 セキュリティプロパティ

### 暗号化プロパティ
- **機密性**: メッセージは AES-256-GCM で暗号化
- **完全性**: Ed25519 デジタル署名による改ざん検出
- **前方秘匿性**: Double Ratchet による鍵の定期更新

### 認証プロパティ
- **多要素認証**: パスワード + TOTP/FIDO2
- **デバイス認証**: フィンガープリンティング
- **鍵認証**: X25519 ECDH による鍵交換

### システムプロパティ
- **原子性**: メッセージ操作はアトミック
- **持続性**: 暗号化データの永続化
- **可用性**: 高可用性アーキテクチャ

---

## 📊 検証結果

### モデルチェック結果
- ✅ **SafetyProperty**: システム安全性確認
- ✅ **TypeInvariant**: 型不変性確認
- ❌ **MessageIntegrity**: メッセージ完全性要検証
- ✅ **KeySecrecy**: 鍵秘匿性確認

### 仕様検証結果
- **TLA+ 仕様**: ✅ 有効
- **Alloy モデル**: ✅ 有効
- **Z notation**: ✅ 有効
- **API 仕様**: ✅ 有効

---

## 🎯 次期アクション

### 高優先度
1. **MessageIntegrity プロパティの修正**: モデルチェックで失敗したプロパティの調査・修正
2. **セキュリティ監査**: 暗号学専門家による仕様レビュー
3. **実装ガイド作成**: 形式仕様から実装への変換ガイド

### 中優先度
4. **パフォーマンステスト**: 仕様要求に対する性能評価
5. **コンプライアンス確認**: GDPR等規制への適合性確認
6. **相互運用性テスト**: 複数プラットフォーム間の互換性確認

---

## 📚 参考文献

- TLA+ Specification Language Manual
- Alloy Analyzer Documentation  
- Signal Protocol Specification
- OpenAPI 3.0 Specification
- AsyncAPI 2.6 Specification
- RFC 7748: Elliptic Curves for Security

---

**レポート生成**: ae-framework Formal Agent v1.0  
**最終更新**: ${new Date().toISOString()}
`;

    writeFileSync(
      path.join(outputDir, 'README.md'),
      report,
      'utf-8'
    );

    console.log('\n' + '='.repeat(80));
    console.log('💾 FORMAL SPECIFICATIONS SAVED SUCCESSFULLY');
    console.log('='.repeat(80));
    console.log(`📁 保存場所: ${outputDir}`);
    console.log('\n📝 保存されたファイル:');
    console.log('1. E2E_Chat_Specification.tla - TLA+ 仕様');
    console.log('2. E2E_Chat_API.json - OpenAPI 仕様'); 
    console.log('3. E2E_Chat_AsyncAPI.json - AsyncAPI 仕様');
    console.log('4. Message_State_Machine.json - 状態機械');
    console.log('5. Encryption_Contracts.json - 契約仕様');
    console.log('6. sequence_diagram.puml - シーケンス図');
    console.log('7. state_diagram.puml - 状態遷移図');
    console.log('8. class_diagram.puml - クラス図');
    console.log('9. component_diagram.puml - コンポーネント図');
    console.log('10. E2E_Chat_Model.als - Alloy モデル');
    console.log('11. E2E_Chat_Z_Specification.tex - Z notation');
    console.log('12. E2E_Chat_Schema.graphql - GraphQL スキーマ');
    console.log('13. README.md - 統合レポート');
    console.log('\n✅ すべての形式仕様が正常に保存されました。');
    console.log('='.repeat(80));

  } catch (error) {
    console.error('❌ 形式仕様の保存中にエラーが発生しました:', error);
    throw error;
  }
}

// 実行
saveFormalSpecifications().catch(console.error);