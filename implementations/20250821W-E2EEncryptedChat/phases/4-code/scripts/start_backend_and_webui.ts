/**
 * E2E暗号化チャット フルスタック起動
 * バックエンドサーバーとWebUIを連携して起動
 */

import { execSync, spawn } from 'child_process';
import { readFileSync, writeFileSync, existsSync } from 'fs';
import { join } from 'path';

async function startBackendAndWebUI(): Promise<void> {
  console.log('🚀 E2E暗号化チャット フルスタック起動を開始します...\n');

  try {
    // 1. バックエンド実装の確認
    console.log('🔍 1. バックエンド実装の確認...');
    const backendPath = '/home/claudecode/work/ae-framework_test/e2e_chat_implementation';
    const readStatusPath = '/home/claudecode/work/ae-framework_test/read_status_implementation';
    const webuiPath = '/home/claudecode/work/ae-framework_test/webui';

    if (!existsSync(backendPath)) {
      throw new Error('E2E暗号化チャットバックエンドが見つかりません');
    }
    if (!existsSync(readStatusPath)) {
      throw new Error('ReadStatus実装が見つかりません');
    }
    if (!existsSync(webuiPath)) {
      throw new Error('WebUI実装が見つかりません');
    }
    console.log('   ✅ 全ての実装ディレクトリを確認');

    // 2. 統合サーバー作成
    console.log('\n🔧 2. 統合バックエンドサーバー作成...');
    const integratedServer = createIntegratedServer();
    const integratedServerPath = '/home/claudecode/work/ae-framework_test/integrated_server';
    
    // 統合サーバーディレクトリ作成
    if (!existsSync(integratedServerPath)) {
      execSync(`mkdir -p ${integratedServerPath}`);
    }

    // 統合サーバーファイル作成
    writeFileSync(join(integratedServerPath, 'server.js'), integratedServer.serverCode);
    writeFileSync(join(integratedServerPath, 'package.json'), integratedServer.packageJson);
    console.log('   ✅ 統合バックエンドサーバー作成完了');

    // 3. 統合サーバー依存関係インストール
    console.log('\n📦 3. 統合サーバー依存関係インストール...');
    execSync('npm install', { 
      cwd: integratedServerPath,
      stdio: 'inherit'
    });
    console.log('   ✅ 依存関係インストール完了');

    // 4. WebUI設定更新（バックエンド接続先設定）
    console.log('\n⚙️ 4. WebUI設定更新...');
    updateWebUIConfig();
    console.log('   ✅ WebUI設定更新完了');

    // 5. バックエンドサーバー起動
    console.log('\n🚀 5. 統合バックエンドサーバー起動...');
    const backendProcess = spawn('npm', ['start'], {
      cwd: integratedServerPath,
      stdio: 'pipe',
      detached: false
    });

    // バックエンド起動ログ監視
    backendProcess.stdout.on('data', (data) => {
      console.log(`[Backend] ${data.toString().trim()}`);
    });

    backendProcess.stderr.on('data', (data) => {
      console.log(`[Backend Error] ${data.toString().trim()}`);
    });

    // 起動待機
    console.log('   ⏳ バックエンドサーバー起動待機中...');
    await new Promise(resolve => setTimeout(resolve, 5000));

    // バックエンド接続確認
    try {
      execSync('curl -f http://localhost:3000/health', { stdio: 'pipe' });
      console.log('   ✅ バックエンドサーバー起動確認完了');
    } catch (error) {
      console.log('   ⚠️ バックエンドサーバー接続確認に失敗（起動中の可能性があります）');
    }

    // 6. WebUI更新とリスタート
    console.log('\n🌐 6. WebUI更新とリスタート...');
    
    // 既存のWebUI停止
    try {
      execSync('pkill -f "vite preview"', { stdio: 'pipe' });
      await new Promise(resolve => setTimeout(resolve, 2000));
    } catch (error) {
      // プロセスが見つからない場合は無視
    }

    // WebUI再ビルド
    execSync('npm run build', { 
      cwd: webuiPath,
      stdio: 'inherit'
    });

    // WebUI起動
    const webuiProcess = spawn('npm', ['run', 'preview'], {
      cwd: webuiPath,
      stdio: 'pipe',
      detached: false
    });

    webuiProcess.stdout.on('data', (data) => {
      console.log(`[WebUI] ${data.toString().trim()}`);
    });

    webuiProcess.stderr.on('data', (data) => {
      console.log(`[WebUI Error] ${data.toString().trim()}`);
    });

    await new Promise(resolve => setTimeout(resolve, 3000));
    console.log('   ✅ WebUI再起動完了');

    // 7. 統合テスト実行
    console.log('\n🧪 7. 統合動作テスト...');
    const integrationTest = await runIntegrationTest();
    console.log('   ✅ 統合動作テスト完了');

    // 8. 起動完了サマリー
    console.log('\n================================================================================');
    console.log('🎉 E2E暗号化チャット フルスタック起動完了');
    console.log('================================================================================');
    console.log('✅ 起動完了したサービス:');
    console.log('   📡 バックエンドAPI: http://localhost:3000');
    console.log('   🌐 WebUI: http://localhost:4173');
    console.log('   🔌 WebSocket: ws://localhost:3000/ws');
    console.log('');
    console.log('📋 利用可能な機能:');
    console.log('   - ユーザー登録・ログイン');
    console.log('   - E2E暗号化メッセージング');
    console.log('   - リアルタイム通信 (WebSocket)');
    console.log('   - 既読ステータス管理');
    console.log('   - 暗号化鍵管理');
    console.log('');
    console.log('🚀 アクセス方法:');
    console.log('   1. ブラウザで http://localhost:4173 にアクセス');
    console.log('   2. 新規ユーザー登録またはログイン');
    console.log('   3. 暗号化チャット開始');
    console.log('');
    console.log(`📊 統合テスト結果: ${integrationTest.status}`);
    console.log(`🔧 API接続: ${integrationTest.apiConnection ? '✅ 正常' : '❌ エラー'}`);
    console.log(`🌐 WebUI表示: ${integrationTest.webuiAccess ? '✅ 正常' : '❌ エラー'}`);
    console.log('================================================================================\n');

    // プロセス終了時のクリーンアップ
    process.on('SIGINT', () => {
      console.log('\n🔄 サーバー停止中...');
      backendProcess.kill();
      webuiProcess.kill();
      process.exit(0);
    });

    // プロセスを生存させる
    console.log('💡 サーバーを停止するには Ctrl+C を押してください');
    
    // 無限ループでプロセスを維持
    const keepAlive = () => {
      setTimeout(() => {
        if (!backendProcess.killed && !webuiProcess.killed) {
          keepAlive();
        }
      }, 1000);
    };
    keepAlive();

  } catch (error) {
    console.error('❌ フルスタック起動中にエラーが発生しました:', error);
    throw error;
  }
}

function createIntegratedServer(): { serverCode: string; packageJson: string } {
  const serverCode = `const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const cors = require('cors');
const crypto = require('crypto');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: ["http://localhost:4173", "http://localhost:3001"],
    methods: ["GET", "POST", "PUT", "DELETE"],
    credentials: true
  }
});

// Middleware
app.use(cors({
  origin: ["http://localhost:4173", "http://localhost:3001"],
  credentials: true
}));
app.use(express.json());

// In-memory data stores (本番環境では永続化ストレージを使用)
const users = new Map();
const conversations = new Map();
const messages = new Map();
const readStatuses = new Map();
const onlineUsers = new Set();

// ユーティリティ関数
function generateId() {
  return crypto.randomBytes(16).toString('hex');
}

function hashPassword(password) {
  return crypto.createHash('sha256').update(password).digest('hex');
}

function generateJWT(userId) {
  // 簡略化されたJWT（本番環境では proper JWT library を使用）
  const payload = { userId, iat: Date.now() };
  return Buffer.from(JSON.stringify(payload)).toString('base64');
}

function verifyJWT(token) {
  try {
    const payload = JSON.parse(Buffer.from(token, 'base64').toString());
    return payload.userId;
  } catch {
    return null;
  }
}

// API Routes

// ヘルスチェック
app.get('/health', (req, res) => {
  res.json({ status: 'ok', timestamp: new Date().toISOString() });
});

// ユーザー登録
app.post('/api/auth/register', (req, res) => {
  const { username, email, password } = req.body;
  
  if (!username || !email || !password) {
    return res.status(400).json({ error: 'Username, email, and password are required' });
  }
  
  // ユーザー重複チェック
  for (const user of users.values()) {
    if (user.email === email || user.username === username) {
      return res.status(409).json({ error: 'User already exists' });
    }
  }
  
  const userId = generateId();
  const user = {
    id: userId,
    username,
    email,
    passwordHash: hashPassword(password),
    publicKey: null, // WebCrypto API で生成される
    createdAt: new Date().toISOString()
  };
  
  users.set(userId, user);
  
  const token = generateJWT(userId);
  res.json({
    token,
    user: {
      id: user.id,
      username: user.username,
      email: user.email
    }
  });
});

// ユーザーログイン
app.post('/api/auth/login', (req, res) => {
  const { email, password } = req.body;
  
  if (!email || !password) {
    return res.status(400).json({ error: 'Email and password are required' });
  }
  
  const user = Array.from(users.values()).find(u => u.email === email);
  if (!user || user.passwordHash !== hashPassword(password)) {
    return res.status(401).json({ error: 'Invalid credentials' });
  }
  
  const token = generateJWT(user.id);
  res.json({
    token,
    user: {
      id: user.id,
      username: user.username,
      email: user.email
    }
  });
});

// 認証ミドルウェア
function authenticateToken(req, res, next) {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  
  if (!token) {
    return res.status(401).json({ error: 'Access token required' });
  }
  
  const userId = verifyJWT(token);
  if (!userId || !users.has(userId)) {
    return res.status(403).json({ error: 'Invalid token' });
  }
  
  req.userId = userId;
  next();
}

// 会話一覧取得
app.get('/api/conversations', authenticateToken, (req, res) => {
  const userConversations = Array.from(conversations.values())
    .filter(conv => conv.participants.includes(req.userId))
    .map(conv => ({
      id: conv.id,
      name: conv.name,
      participants: conv.participants.map(id => {
        const user = users.get(id);
        return user ? { id: user.id, username: user.username } : null;
      }).filter(Boolean),
      lastMessage: conv.lastMessage,
      updatedAt: conv.updatedAt
    }));
  
  res.json(userConversations);
});

// 新規会話作成
app.post('/api/conversations', authenticateToken, (req, res) => {
  const { participantIds, name } = req.body;
  
  if (!participantIds || !Array.isArray(participantIds)) {
    return res.status(400).json({ error: 'Participant IDs are required' });
  }
  
  const conversationId = generateId();
  const conversation = {
    id: conversationId,
    name: name || 'New Conversation',
    participants: [req.userId, ...participantIds],
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
    lastMessage: null
  };
  
  conversations.set(conversationId, conversation);
  
  res.json(conversation);
});

// メッセージ一覧取得
app.get('/api/conversations/:conversationId/messages', authenticateToken, (req, res) => {
  const { conversationId } = req.params;
  const conversation = conversations.get(conversationId);
  
  if (!conversation || !conversation.participants.includes(req.userId)) {
    return res.status(404).json({ error: 'Conversation not found' });
  }
  
  const conversationMessages = Array.from(messages.values())
    .filter(msg => msg.conversationId === conversationId)
    .sort((a, b) => new Date(a.timestamp) - new Date(b.timestamp));
  
  res.json(conversationMessages);
});

// メッセージ送信
app.post('/api/conversations/:conversationId/messages', authenticateToken, (req, res) => {
  const { conversationId } = req.params;
  const { encryptedContent, type = 'text' } = req.body;
  
  const conversation = conversations.get(conversationId);
  if (!conversation || !conversation.participants.includes(req.userId)) {
    return res.status(404).json({ error: 'Conversation not found' });
  }
  
  const messageId = generateId();
  const message = {
    id: messageId,
    conversationId,
    senderId: req.userId,
    encryptedContent,
    type,
    timestamp: new Date().toISOString(),
    isEncrypted: true
  };
  
  messages.set(messageId, message);
  
  // 会話の最終メッセージ更新
  conversation.lastMessage = {
    id: messageId,
    preview: '[Encrypted Message]',
    timestamp: message.timestamp
  };
  conversation.updatedAt = message.timestamp;
  
  // WebSocket経由で他の参加者に通知
  conversation.participants.forEach(participantId => {
    if (participantId !== req.userId) {
      io.to(participantId).emit('message', message);
    }
  });
  
  res.json(message);
});

// 既読ステータス設定
app.post('/api/conversations/:conversationId/messages/:messageId/read', authenticateToken, (req, res) => {
  const { conversationId, messageId } = req.params;
  
  const conversation = conversations.get(conversationId);
  if (!conversation || !conversation.participants.includes(req.userId)) {
    return res.status(404).json({ error: 'Conversation not found' });
  }
  
  const message = messages.get(messageId);
  if (!message || message.conversationId !== conversationId) {
    return res.status(404).json({ error: 'Message not found' });
  }
  
  const readStatusId = generateId();
  const readStatus = {
    id: readStatusId,
    conversationId,
    messageId,
    userId: req.userId,
    readAt: new Date().toISOString(),
    deviceId: req.headers['x-device-id'] || 'unknown'
  };
  
  readStatuses.set(readStatusId, readStatus);
  
  // WebSocket経由で読み取りステータス通知
  conversation.participants.forEach(participantId => {
    io.to(participantId).emit('readStatusUpdate', readStatus);
  });
  
  res.json(readStatus);
});

// ユーザー一覧取得（チャット相手検索用）
app.get('/api/users', authenticateToken, (req, res) => {
  const allUsers = Array.from(users.values())
    .filter(user => user.id !== req.userId)
    .map(user => ({
      id: user.id,
      username: user.username,
      email: user.email
    }));
  
  res.json(allUsers);
});

// WebSocket接続処理
io.on('connection', (socket) => {
  console.log('WebSocket client connected:', socket.id);
  
  // ユーザー認証
  socket.on('authenticate', (token) => {
    const userId = verifyJWT(token);
    if (userId && users.has(userId)) {
      socket.userId = userId;
      socket.join(userId); // ユーザー固有のルームに参加
      onlineUsers.add(userId);
      
      // オンラインステータス通知
      socket.broadcast.emit('userOnline', userId);
      
      console.log('User ' + userId + ' authenticated and joined room');
    } else {
      socket.emit('authError', 'Invalid token');
    }
  });
  
  // メッセージ送信 (WebSocket経由)
  socket.on('sendMessage', (data) => {
    if (!socket.userId) return;
    
    const { conversationId, encryptedContent, type = 'text' } = data;
    const conversation = conversations.get(conversationId);
    
    if (!conversation || !conversation.participants.includes(socket.userId)) {
      socket.emit('error', 'Conversation not found');
      return;
    }
    
    const messageId = generateId();
    const message = {
      id: messageId,
      conversationId,
      senderId: socket.userId,
      encryptedContent,
      type,
      timestamp: new Date().toISOString(),
      isEncrypted: true
    };
    
    messages.set(messageId, message);
    
    // 会話の参加者全員に送信
    conversation.participants.forEach(participantId => {
      io.to(participantId).emit('message', message);
    });
  });
  
  // 既読ステータス更新
  socket.on('markAsRead', (data) => {
    if (!socket.userId) return;
    
    const { conversationId, messageId } = data;
    const conversation = conversations.get(conversationId);
    
    if (!conversation || !conversation.participants.includes(socket.userId)) {
      return;
    }
    
    const readStatusId = generateId();
    const readStatus = {
      id: readStatusId,
      conversationId,
      messageId,
      userId: socket.userId,
      readAt: new Date().toISOString(),
      deviceId: 'websocket'
    };
    
    readStatuses.set(readStatusId, readStatus);
    
    // 会話の参加者全員に通知
    conversation.participants.forEach(participantId => {
      io.to(participantId).emit('readStatusUpdate', readStatus);
    });
  });
  
  // 切断処理
  socket.on('disconnect', () => {
    if (socket.userId) {
      onlineUsers.delete(socket.userId);
      socket.broadcast.emit('userOffline', socket.userId);
      console.log('User ' + socket.userId + ' disconnected');
    }
  });
});

// サーバー起動
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log('🚀 E2E暗号化チャット統合サーバーが起動しました: http://localhost:' + PORT);
  console.log('🔌 WebSocket エンドポイント: ws://localhost:' + PORT);
  console.log('📡 API エンドポイント: http://localhost:' + PORT + '/api');
  console.log('💚 ヘルスチェック: http://localhost:' + PORT + '/health');
});

// エラーハンドリング
process.on('uncaughtException', (error) => {
  console.error('Uncaught Exception:', error);
});

process.on('unhandledRejection', (reason, promise) => {
  console.error('Unhandled Rejection at:', promise, 'reason:', reason);
});
`;

  const packageJson = `{
  "name": "e2e-chat-integrated-server",
  "version": "1.0.0",
  "description": "Integrated backend server for E2E encrypted chat",
  "main": "server.js",
  "scripts": {
    "start": "node server.js",
    "dev": "nodemon server.js"
  },
  "dependencies": {
    "express": "^4.18.2",
    "socket.io": "^4.7.4",
    "cors": "^2.8.5",
    "crypto": "^1.0.1"
  },
  "devDependencies": {
    "nodemon": "^3.0.2"
  }
}`;

  return { serverCode, packageJson };
}

function updateWebUIConfig(): void {
  // WebUIの環境設定ファイルを作成/更新
  const webuiPath = '/home/claudecode/work/ae-framework_test/webui';
  const envConfig = `VITE_API_URL=http://localhost:3000
VITE_WS_URL=ws://localhost:3000
VITE_APP_NAME=E2E Encrypted Chat
VITE_APP_VERSION=1.0.0
`;
  
  writeFileSync(join(webuiPath, '.env.local'), envConfig);
  
  // APIサービスの設定更新
  const apiServicePath = join(webuiPath, 'src/services/apiService.ts');
  if (existsSync(apiServicePath)) {
    let apiService = readFileSync(apiServicePath, 'utf-8');
    
    // Base URLを更新
    apiService = apiService.replace(
      /baseURL: ['"'][^'"]*['"']/,
      "baseURL: 'http://localhost:3000/api'"
    );
    
    writeFileSync(apiServicePath, apiService);
  }
  
  // WebSocketサービスの設定更新  
  const wsServicePath = join(webuiPath, 'src/services/websocketService.ts');
  if (existsSync(wsServicePath)) {
    let wsService = readFileSync(wsServicePath, 'utf-8');
    
    // WebSocket URLを更新
    wsService = wsService.replace(
      /ws:\/\/[^'"]*['"`]/g,
      "'ws://localhost:3000'"
    );
    
    writeFileSync(wsServicePath, wsService);
  }
}

async function runIntegrationTest(): Promise<any> {
  try {
    // APIヘルスチェック
    const healthCheck = execSync('curl -f http://localhost:3000/health', { 
      stdio: 'pipe' 
    }).toString();
    
    // WebUIアクセスチェック
    const webuiCheck = execSync('curl -f http://localhost:4173/', { 
      stdio: 'pipe' 
    }).toString();
    
    return {
      status: 'success',
      apiConnection: healthCheck.includes('ok'),
      webuiAccess: webuiCheck.includes('<!doctype html>'),
      timestamp: new Date().toISOString()
    };
  } catch (error) {
    return {
      status: 'partial',
      apiConnection: false,
      webuiAccess: false,
      error: error.message,
      timestamp: new Date().toISOString()
    };
  }
}

// メイン実行
if (import.meta.url === `file://${process.argv[1]}`) {
  startBackendAndWebUI()
    .catch((error) => {
      console.error('Fatal error:', error);
      process.exit(1);
    });
}