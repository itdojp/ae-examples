import { Server, Socket } from 'socket.io';
import jwt from 'jsonwebtoken';
import { MessageEvent } from '@e2e-chat/shared';

const JWT_SECRET = process.env.JWT_SECRET || 'dev-secret-change-in-production';

interface AuthenticatedSocket extends Socket {
  userId?: string;
  userEmail?: string;
}

export function setupSocketHandlers(io: Server) {
  // Authentication middleware
  io.use((socket: AuthenticatedSocket, next) => {
    try {
      const token = socket.handshake.auth.token;
      if (!token) {
        return next(new Error('Authentication error'));
      }

      const decoded = jwt.verify(token, JWT_SECRET) as { userId: string; email: string };
      socket.userId = decoded.userId;
      socket.userEmail = decoded.email;

      next();
    } catch (err) {
      next(new Error('Authentication error'));
    }
  });

  io.on('connection', (socket: AuthenticatedSocket) => {
    console.log(`User connected: ${socket.userId}`);

    // Join user's personal room
    if (socket.userId) {
      socket.join(socket.userId);
      
      // Broadcast online status
      socket.broadcast.emit('presence', {
        type: 'presence',
        data: { userId: socket.userId, status: 'online' }
      } as MessageEvent);
    }

    // Handle joining a chat room
    socket.on('join-chat', (otherUserId: string) => {
      const roomId = [socket.userId, otherUserId].sort().join('-');
      socket.join(roomId);
      console.log(`User ${socket.userId} joined room ${roomId}`);
    });

    // Handle sending messages
    socket.on('send-message', (data: any) => {
      const { recipientId, message } = data;
      
      // Send to recipient
      io.to(recipientId).emit('new-message', {
        type: 'message',
        data: message
      } as MessageEvent);

      // Also send to room for both users to see
      const roomId = [socket.userId, recipientId].sort().join('-');
      socket.to(roomId).emit('new-message', {
        type: 'message',
        data: message
      } as MessageEvent);
    });

    // Handle typing indicators
    socket.on('typing', (data: { recipientId: string; isTyping: boolean }) => {
      io.to(data.recipientId).emit('typing-update', {
        type: 'typing',
        data: { userId: socket.userId, isTyping: data.isTyping }
      } as MessageEvent);
    });

    // Handle session verification
    socket.on('verify-session', (data: { sessionId: string; verified: boolean }) => {
      const { sessionId, verified } = data;
      
      // Broadcast to all participants
      socket.broadcast.emit('session-verified', {
        type: 'session_verified',
        data: { sessionId, verified }
      } as MessageEvent);
    });

    // Handle disconnection
    socket.on('disconnect', () => {
      console.log(`User disconnected: ${socket.userId}`);
      
      if (socket.userId) {
        // Broadcast offline status
        socket.broadcast.emit('presence', {
          type: 'presence',
          data: { userId: socket.userId, status: 'offline' }
        } as MessageEvent);
      }
    });
  });
}