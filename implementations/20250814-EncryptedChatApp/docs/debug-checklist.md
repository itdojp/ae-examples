# 🔍 簡易版WebUI デバッグチェックリスト

## 事前確認

### サーバー状態確認
```bash
# バックエンドサーバー確認
curl http://localhost:3000/health
# → {"status":"ok","timestamp":"..."}

# WebUIサーバー確認  
curl http://localhost:4173/ | grep title
# → <title>E2E Chat - Secure Messaging</title>
```

## 📱 ブラウザでの確認手順

### 1. 開発者ツール準備
1. **F12** または **右クリック → 検証** で開発者ツールを開く
2. **Console** タブを選択
3. **Network** タブも開いておく (APIリクエスト監視用)
4. **Application** タブも開いておく (LocalStorage確認用)

### 2. 初期表示確認
- [ ] 🔧 Auth Debug Tool が表示される
- [ ] Email/Password フィールドが表示される
- [ ] 3つのボタンが表示される
- [ ] コンソールに `=== Minimal App Starting ===` が出力される

### 3. Check State テスト
**手順**: Check State ボタンをクリック
**確認項目**:
- [ ] アラートが表示される
- [ ] JSON形式でenvVarsが表示される
- [ ] VITE_API_URL が正しい値

### 4. Test Login テスト (最重要)
**手順**: Test Login ボタンをクリック
**確認項目**:
- [ ] コンソールに `=== Direct API Test ===` が出力
- [ ] Networkタブにリクエストが表示される
- [ ] レスポンス status が 200
- [ ] アラートにSUCCESSが表示される
- [ ] 2秒後にページがリロードされる

### 5. Test Registration テスト
**手順**: Test Registration ボタンをクリック
**確認項目**:
- [ ] 新規ユーザーが作成される
- [ ] アラートにREGISTRATION SUCCESSが表示される

## 🚨 エラーパターンと対処

### パターン1: ページが表示されない
**症状**: 白い画面または読み込みエラー
**確認**:
- Console タブでJavaScriptエラーを確認
- Network タブで失敗したリクエストを確認
- Sources タブでファイル読み込み状況を確認

### パターン2: ボタンをクリックしても反応しない
**症状**: ボタンクリック時に何も起こらない
**確認**:
- Console でJavaScriptエラーを確認
- Elements タブでDOMが正しく生成されているか
- Event listeners が正しく設定されているか

### パターン3: API呼び出しが失敗
**症状**: "FAILED" や "ERROR" がアラートに表示
**確認**:
- Network タブでリクエストの詳細を確認
- Headers を確認 (CORS関連)
- Response body を確認

### パターン4: CORS エラー
**症状**: Console に CORS 関連エラー
**エラー例**:
```
Access to fetch at 'http://localhost:3000/api/auth/login' from origin 'http://localhost:4173' has been blocked by CORS policy
```
**対処**: バックエンドサーバーの再起動

## 📊 データ収集項目

### 必須データ
1. **Console ログ全体** (コピー&ペースト)
2. **Network タブのリクエスト詳細**
   - URL
   - Method
   - Status Code
   - Request Headers
   - Response Headers
   - Request Body
   - Response Body
3. **エラーがある場合のエラーメッセージ**

### 追加データ (問題がある場合)
1. **Application タブ**
   - Local Storage の内容
   - Session Storage の内容
2. **Sources タブ**
   - JavaScript ファイルの読み込み状況
3. **Elements タブ**
   - DOM 構造の確認

## 🎯 判定基準

### ✅ 成功判定
- Test Login で SUCCESS アラートが表示される
- コンソールエラーがない
- ページリロード後も正常動作

### ❌ 失敗判定  
- JavaScript エラーが発生
- API リクエストが失敗 (status 200以外)
- アラートに ERROR や FAILED が表示

### ⚠️ 部分成功
- 画面は表示されるがボタンが動作しない
- API リクエストは成功するが認証状態が保存されない

## 📋 テスト実行チェックシート

```
□ 開発者ツールを開いた
□ 初期表示を確認した
□ Check State をテストした
□ Test Login をテストした  
□ Test Registration をテストした
□ コンソールログを保存した
□ Network タブのデータを確認した
□ エラーがある場合は詳細を記録した
```

このチェックリストに従ってテストを実行し、結果をお知らせください。