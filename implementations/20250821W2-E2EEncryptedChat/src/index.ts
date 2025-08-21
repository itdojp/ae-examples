/**
 * E2E Encrypted Chat Application
 * Main entry point
 */

import { RealtimeServer } from './server/websocket-server.js';
import { InMemoryRepository } from './repository/in-memory-repository.js';
import { ChatService } from './services/chat-service.js';
import { User } from './domain/entities.js';
import express from 'express';
import { v4 as uuidv4 } from 'uuid';

// Initialize repository
const repository = new InMemoryRepository();

// Start WebSocket server
const wsServer = new RealtimeServer(8080);

// Create Express app for REST API
const app = express();
app.use(express.json());

// CORS middleware
app.use((req, res, next) => {
  res.header('Access-Control-Allow-Origin', '*');
  res.header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
  res.header('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  if (req.method === 'OPTIONS') {
    res.sendStatus(200);
  } else {
    next();
  }
});

// Authentication endpoint
app.post('/api/auth/register', async (req, res) => {
  try {
    const { email, displayName, password } = req.body;
    
    // Check if user exists
    const existingUser = await repository.getUserByEmail(email);
    if (existingUser) {
      return res.status(400).json({ error: 'User already exists' });
    }

    // Create dummy user for demo
    const dummyUser: User = {
      id: uuidv4(),
      email,
      displayName,
      createdAt: new Date(),
      devices: [],
      trustLevel: 'unverified',
      publicKey: ''
    };

    // Initialize chat service and create user with keys
    const chatService = new ChatService(repository, dummyUser);
    const user = await chatService.initializeUser(email, displayName);

    // Generate token (simplified for demo)
    const token = Buffer.from(`${user.id}:${Date.now()}`).toString('base64');

    res.json({
      user: {
        id: user.id,
        email: user.email,
        displayName: user.displayName
      },
      token
    });
  } catch (error) {
    console.error('Registration error:', error);
    res.status(500).json({ error: 'Registration failed' });
  }
});

app.post('/api/auth/login', async (req, res) => {
  try {
    const { email, password } = req.body;
    
    const user = await repository.getUserByEmail(email);
    if (!user) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }

    // Generate token (simplified for demo)
    const token = Buffer.from(`${user.id}:${Date.now()}`).toString('base64');

    res.json({
      user: {
        id: user.id,
        email: user.email,
        displayName: user.displayName
      },
      token
    });
  } catch (error) {
    console.error('Login error:', error);
    res.status(500).json({ error: 'Login failed' });
  }
});

// User endpoints
app.get('/api/users/:userId', async (req, res) => {
  try {
    const user = await repository.getUser(req.params.userId);
    if (!user) {
      return res.status(404).json({ error: 'User not found' });
    }
    
    res.json({
      id: user.id,
      displayName: user.displayName,
      trustLevel: user.trustLevel,
      publicKey: user.publicKey
    });
  } catch (error) {
    res.status(500).json({ error: 'Failed to fetch user' });
  }
});

// Session endpoints
app.post('/api/sessions', async (req, res) => {
  try {
    const { userId, recipientId } = req.body;
    const authHeader = req.headers.authorization;
    
    if (!authHeader) {
      return res.status(401).json({ error: 'Unauthorized' });
    }

    const user = await repository.getUser(userId);
    if (!user) {
      return res.status(404).json({ error: 'User not found' });
    }

    const chatService = new ChatService(repository, user);
    const session = await chatService.startSession(recipientId);

    res.json(session);
  } catch (error) {
    console.error('Session creation error:', error);
    res.status(500).json({ error: 'Failed to create session' });
  }
});

app.get('/api/sessions/:sessionId/messages', async (req, res) => {
  try {
    const messages = await repository.getMessages(req.params.sessionId);
    res.json(messages);
  } catch (error) {
    res.status(500).json({ error: 'Failed to fetch messages' });
  }
});

// Key bundle endpoint
app.get('/api/keys/:userId', async (req, res) => {
  try {
    const keyBundle = await repository.getKeyBundle(req.params.userId);
    if (!keyBundle) {
      return res.status(404).json({ error: 'Key bundle not found' });
    }
    
    // Consume one-time pre-key
    const oneTimeKey = await repository.consumeOneTimePreKey(req.params.userId);
    
    res.json({
      identityKey: keyBundle.identityKey,
      signedPreKey: keyBundle.signedPreKey,
      oneTimePreKey: oneTimeKey
    });
  } catch (error) {
    res.status(500).json({ error: 'Failed to fetch keys' });
  }
});

// Security verification endpoint
app.post('/api/sessions/:sessionId/verify', async (req, res) => {
  try {
    const { userId, securityNumber } = req.body;
    
    const user = await repository.getUser(userId);
    if (!user) {
      return res.status(404).json({ error: 'User not found' });
    }

    const chatService = new ChatService(repository, user);
    const verified = await chatService.verifySession(
      req.params.sessionId,
      securityNumber
    );

    res.json({ verified });
  } catch (error) {
    res.status(500).json({ error: 'Verification failed' });
  }
});

// Health check
app.get('/health', (req, res) => {
  res.json({ 
    status: 'healthy',
    service: 'E2E Chat API',
    timestamp: new Date()
  });
});

// Start REST API server
const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`E2E Chat REST API running on port ${PORT}`);
  console.log(`WebSocket server running on port 8080`);
  console.log('\nEndpoints:');
  console.log('  POST /api/auth/register - Register new user');
  console.log('  POST /api/auth/login - Login user');
  console.log('  GET  /api/users/:userId - Get user info');
  console.log('  POST /api/sessions - Create chat session');
  console.log('  GET  /api/sessions/:sessionId/messages - Get messages');
  console.log('  GET  /api/keys/:userId - Get key bundle');
  console.log('  POST /api/sessions/:sessionId/verify - Verify session');
  console.log('  WS   ws://localhost:8080/ws - WebSocket connection');
});

// Graceful shutdown
process.on('SIGTERM', () => {
  console.log('SIGTERM signal received: closing servers');
  process.exit(0);
});

process.on('SIGINT', () => {
  console.log('SIGINT signal received: closing servers');
  process.exit(0);
});