# 簡易版WebUI テストシナリオ

## 📋 テスト環境確認

### 前提条件
- バックエンドサーバー: http://localhost:3000 (稼働中)
- WebUI: http://localhost:4173 (簡易版デプロイ済み)
- ブラウザ: 開発者ツール(F12)でコンソールタブを開く

## 🎯 テストシナリオ

### シナリオ1: 基本動作確認
**目的**: 簡易版WebUIが正常に表示されるか確認

**手順**:
1. ブラウザで http://localhost:4173 にアクセス
2. ページが読み込まれるまで待機
3. 画面表示を確認

**期待結果**:
- 🔧 Auth Debug Tool という見出しが表示される
- Email/Passwordフィールドが表示される
- 3つのボタンが表示される: "Test Login", "Test Registration", "Check State"

**取得データ**:
- ページタイトル
- 表示されている要素の確認
- 初期コンソールメッセージ: "=== Minimal App Starting ==="

---

### シナリオ2: 環境変数・設定確認
**目的**: 環境変数とWebUI設定が正しく読み込まれているか確認

**手順**:
1. "Check State" ボタンをクリック
2. アラート表示を確認
3. コンソールログを確認

**期待結果**:
- アラート表示: 環境変数情報が表示される
- VITE_API_URL: http://localhost:3000
- VITE_WS_URL: ws://localhost:3000

**取得データ**:
```json
{
  "hasToken": false,
  "tokenPreview": null,
  "envVars": {
    "VITE_API_URL": "http://localhost:3000",
    "VITE_WS_URL": "ws://localhost:3000"
  }
}
```

---

### シナリオ3: 既存ユーザーログインテスト
**目的**: 既存ユーザーでのログイン機能確認

**手順**:
1. Email: `test@example.com`
2. Password: `password123`
3. "Test Login" ボタンをクリック
4. アラート表示とコンソールログを確認

**期待結果**:
- アラート: "SUCCESS: {token: "...", user: {...}}" 表示
- 2秒後にページがリロード
- リロード後、Check Stateでトークンが保存されていることを確認

**取得データ**:
```json
{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "user": {
    "id": "ba892ae1c19f50f013bdb7c4cffa19ed",
    "username": "testuser",
    "email": "test@example.com"
  }
}
```

**コンソールログ**:
- "=== Direct API Test ==="
- "Response status: 200"
- "Response headers: [...]"
- "Login success: {token: "...", user: {...}}"

---

### シナリオ4: 新規ユーザー登録テスト
**目的**: 新規ユーザー登録機能確認

**手順**:
1. "Test Registration" ボタンをクリック
2. アラート表示とコンソールログを確認

**期待結果**:
- アラート: "REGISTRATION SUCCESS: {token: "...", user: {...}}" 表示
- 新しいユーザー情報が返される

**取得データ**:
```json
{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "user": {
    "id": "新しいユーザーID",
    "username": "testuser[タイムスタンプ]",
    "email": "test[タイムスタンプ]@example.com"
  }
}
```

---

### シナリオ5: エラーハンドリングテスト
**目的**: バックエンドが停止している場合のエラー処理確認

**手順**:
1. バックエンドサーバーを停止 (別ターミナルで Ctrl+C)
2. "Test Login" ボタンをクリック
3. エラー表示を確認

**期待結果**:
- アラート: "ERROR: Failed to fetch" または類似のネットワークエラー
- コンソール: 詳細なエラーメッセージ

**取得データ**:
- エラーメッセージの詳細
- ネットワークエラーの種類
- fetch APIの動作確認

---

## 📊 重要な取得データ

### 1. コンソールログ (最重要)
```
=== Minimal App Starting ===
Environment: {API_URL: "http://localhost:3000", WS_URL: "ws://localhost:3000"}
=== Direct API Test ===
Response status: 200
Response headers: [array of headers]
Login success: {response data}
```

### 2. ネットワークタブ (開発者ツール)
- リクエストURL: http://localhost:3000/api/auth/login
- リクエストメソッド: POST
- レスポンスステータス: 200
- レスポンスヘッダー: CORS関連
- リクエスト/レスポンスボディ

### 3. アプリケーションタブ (開発者ツール)
- LocalStorage: authToken の保存確認
- Session Storage: データ確認

### 4. エラーがある場合
- エラーメッセージの詳細
- スタックトレース
- 失敗したリクエストの詳細

## 🚨 問題切り分けポイント

### ✅ 成功した場合
→ **元のWebUIの問題はRedux/状態管理にある**
→ 複雑な認証フローが原因

### ❌ 失敗した場合
**エラー内容による判断**:
- `Failed to fetch` → CORS/ネットワーク問題
- `TypeError` → JavaScript実行エラー
- `404/500` → バックエンドAPI問題
- `SyntaxError` → JSONパース問題

## 📝 テスト結果報告フォーマット

```
## テスト結果

### 基本動作: ✅/❌
- 画面表示: 
- ボタン動作: 

### ログインテスト: ✅/❌
- アラート表示: 
- コンソールログ: 
- トークン保存: 

### 登録テスト: ✅/❌
- 結果: 

### エラー (ある場合):
- エラーメッセージ: 
- コンソールエラー: 
- ネットワークエラー: 

### コンソールログ全体:
[コンソールに表示された全てのログをコピー]
```

このテストにより、**簡易版が動作するかどうか**で元の問題の原因を特定できます。