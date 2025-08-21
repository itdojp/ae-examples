#!/bin/bash
# E2E暗号化チャット クイックスタート

echo "🚀 E2E暗号化チャットアプリケーション起動中..."

# 現在のディレクトリを保存
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# 依存関係のチェック
echo "📦 依存関係チェック中..."

# バックエンド依存関係
if [ ! -d "$SCRIPT_DIR/backend/node_modules" ]; then
    echo "   バックエンド依存関係をインストール中..."
    cd "$SCRIPT_DIR/backend"
    npm install
fi

# WebUI依存関係
if [ ! -d "$SCRIPT_DIR/webui/node_modules" ]; then
    echo "   WebUI依存関係をインストール中..."
    cd "$SCRIPT_DIR/webui"
    npm install
fi

echo "✅ 依存関係チェック完了"

# バックエンドサーバー起動
echo "🔧 バックエンドサーバー起動中..."
cd "$SCRIPT_DIR/backend"
npm start &
BACKEND_PID=$!

# 起動待機
sleep 3

# ヘルスチェック
echo "🔍 バックエンドヘルスチェック..."
if curl -s http://localhost:3000/health > /dev/null; then
    echo "✅ バックエンドサーバー正常起動"
else
    echo "❌ バックエンドサーバー起動失敗"
    exit 1
fi

# WebUIビルド
echo "🏗️ WebUIビルド中..."
cd "$SCRIPT_DIR/webui"
npm run build

# WebUI起動
echo "🌐 WebUI起動中..."
npm run preview &
WEBUI_PID=$!

# 起動待機
sleep 3

echo ""
echo "=================================================================================="
echo "🎉 E2E暗号化チャットアプリケーション起動完了"
echo "=================================================================================="
echo ""
echo "📱 アクセス情報:"
echo "   WebUI:      http://localhost:4173"
echo "   Backend:    http://localhost:3000"
echo "   Health:     http://localhost:3000/health"
echo ""
echo "🔧 テスト方法:"
echo "   1. ブラウザで http://localhost:4173 にアクセス"
echo "   2. 🔧 Auth Debug Tool 画面が表示されることを確認"
echo "   3. 'Test Login' ボタンをクリック"
echo "   4. 開発者ツール(F12)でコンソールログを確認"
echo ""
echo "📋 テストアカウント:"
echo "   Email:    test@example.com"
echo "   Password: password123"
echo ""
echo "🛑 停止方法: Ctrl+C"
echo "=================================================================================="

# クリーンアップ関数
cleanup() {
    echo ""
    echo "🔄 サーバー停止中..."
    if [ ! -z "$BACKEND_PID" ]; then
        kill $BACKEND_PID 2>/dev/null
    fi
    if [ ! -z "$WEBUI_PID" ]; then
        kill $WEBUI_PID 2>/dev/null
    fi
    echo "✅ 停止完了"
    exit 0
}

# シグナルハンドラー
trap cleanup SIGINT SIGTERM

# プロセス維持
echo "💡 アプリケーション実行中... (Ctrl+C で停止)"
wait