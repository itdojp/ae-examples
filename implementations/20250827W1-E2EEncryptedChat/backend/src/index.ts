import express from 'express';
import { createServer } from 'http';
import { Server } from 'socket.io';
import cors from 'cors';
import dotenv from 'dotenv';
import { authRouter } from './routes/auth.js';
import { messagesRouter } from './routes/messages.js';
import { keysRouter } from './routes/keys.js';
import { setupSocketHandlers } from './socket/handlers.js';
import { initializeDatabase } from './services/database.js';

dotenv.config();

const app = express();
const httpServer = createServer(app);
const io = new Server(httpServer, {
  cors: {
    origin: process.env.FRONTEND_URL || 'http://localhost:3000',
    credentials: true
  }
});

const PORT = process.env.PORT || 3001;

// Middleware
app.use(cors({
  origin: process.env.FRONTEND_URL || 'http://localhost:3000',
  credentials: true
}));
app.use(express.json());

// Routes
app.use('/api/auth', authRouter);
app.use('/api/messages', messagesRouter);
app.use('/api/keys', keysRouter);

// Health check
app.get('/health', (req, res) => {
  res.json({ status: 'ok', timestamp: new Date().toISOString() });
});

// Socket.io handlers
setupSocketHandlers(io);

// Initialize database and start server
async function start() {
  try {
    await initializeDatabase();
    
    httpServer.listen(PORT, () => {
      console.log(`🚀 E2E Chat Server running on port ${PORT}`);
      console.log(`🔒 Encryption: Enabled`);
      console.log(`🌐 CORS: ${process.env.FRONTEND_URL || 'http://localhost:3000'}`);
    });
  } catch (error) {
    console.error('Failed to start server:', error);
    process.exit(1);
  }
}

start();