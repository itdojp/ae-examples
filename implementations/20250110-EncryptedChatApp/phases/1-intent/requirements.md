# E2E Encrypted Chat Application Requirements Specification

## 1. プロジェクト概要

### 1.1 目的
エンドツーエンド暗号化を実装した安全なリアルタイムチャットアプリケーションの開発。Signal Protocolを使用し、Perfect Forward Secrecyを保証する。

### 1.2 スコープ
- ユーザー認証・登録
- E2E暗号化メッセージング
- 鍵管理
- リアルタイム通信
- セキュリティ検証

## 2. 機能要件

### 2.1 ユーザー管理
- ユーザー登録（Email/Password）
- ログイン/ログアウト
- 2要素認証（TOTP）
- デバイス管理
- プロファイル管理

### 2.2 暗号化
- Signal Protocol実装
  - Double Ratchet Algorithm
  - X3DH鍵交換
- AES-256-GCM暗号化
- Ed25519署名
- X25519鍵交換

### 2.3 メッセージング
- テキストメッセージ送受信
- メッセージ配信確認
- 既読確認
- タイピングインジケーター
- メッセージ履歴

### 2.4 鍵管理
- Identity Key生成・管理
- Signed Pre-Key生成・ローテーション
- One-time Pre-Key生成・管理
- 安全番号（Safety Number）生成・検証

### 2.5 セッション管理
- X3DHによるセッション確立
- Double Ratchetによる鍵更新
- セッション終了

## 3. 非機能要件

### 3.1 セキュリティ
- Perfect Forward Secrecy
- メッセージの機密性
- メッセージの完全性
- 送信者認証
- Man-in-the-Middle攻撃対策

### 3.2 パフォーマンス
- メッセージ暗号化: < 100ms
- 鍵生成: < 500ms
- WebSocket遅延: < 200ms

### 3.3 可用性
- 99.9% アップタイム
- 自動再接続
- オフラインメッセージ配信

### 3.4 スケーラビリティ
- 10,000同時接続対応
- 水平スケーリング対応

## 4. 技術仕様

### 4.1 暗号化仕様
- **対称暗号**: AES-256-GCM
- **鍵交換**: X25519 (Curve25519)
- **署名**: Ed25519
- **ハッシュ**: SHA-256
- **KDF**: HKDF
- **パスワードハッシュ**: Argon2id

### 4.2 プロトコル仕様
- **Signal Protocol v3**
- **Double Ratchet**: 継続的な鍵更新
- **X3DH**: 非同期鍵交換
- **WebSocket**: リアルタイム通信

## 5. データモデル

### 5.1 ユーザー
- ID (UUID)
- Email
- Password Hash
- Display Name
- 2FA設定

### 5.2 デバイス
- Device ID
- User ID
- Device Fingerprint
- Registration Date

### 5.3 鍵
- Identity Key Pair
- Signed Pre-Key
- One-time Pre-Keys
- Session Keys

### 5.4 メッセージ
- Message ID
- Sender ID
- Recipient ID
- Ciphertext
- Nonce
- Auth Tag
- Timestamp

## 6. API仕様

### 6.1 認証API
- POST /auth/register
- POST /auth/login
- POST /auth/logout
- POST /auth/2fa/enable
- POST /auth/2fa/verify

### 6.2 鍵管理API
- POST /keys/upload
- GET /keys/bundle/:userId
- POST /keys/rotate/signed
- POST /keys/one-time/:userId

### 6.3 メッセージングAPI
- POST /messages/send
- GET /messages/:userId
- POST /messages/:messageId/receipt
- POST /sessions/:userId
- GET /verification/:userId/safety-number

## 7. コンプライアンス

### 7.1 データ保護
- GDPR準拠
- データ最小化原則
- ユーザーデータ削除権

### 7.2 監査
- 全アクセスログ記録
- 暗号化操作の監査証跡
- セキュリティイベント記録

## 8. テスト要件

### 8.1 単体テスト
- 暗号化関数
- 鍵生成
- プロトコル実装

### 8.2 統合テスト
- API エンドポイント
- データベース操作
- WebSocket通信

### 8.3 E2Eテスト
- 完全なメッセージフロー
- 鍵交換フロー
- エラーハンドリング

### 8.4 セキュリティテスト
- ペネトレーションテスト
- 暗号化強度検証
- プロトコル準拠性検証

## 9. 制約事項

- libsodium使用必須
- PostgreSQL使用
- Node.js/TypeScript実装
- ae-framework準拠