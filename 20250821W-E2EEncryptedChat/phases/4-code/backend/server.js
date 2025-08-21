const express = require('express');
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
