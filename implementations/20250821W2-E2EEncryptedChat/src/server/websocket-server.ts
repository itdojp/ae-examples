/**
 * WebSocket Server for Real-time Encrypted Messaging
 */

import { WebSocketServer, WebSocket } from 'ws';
import { createServer } from 'http';
import express from 'express';
import { Message, User, ChatSession } from '../domain/entities.js';
import { v4 as uuidv4 } from 'uuid';

interface WSMessage {
  type: 'auth' | 'message' | 'typing' | 'read' | 'presence' | 'key_exchange' | 'message_ack' | 'error';
  payload: any;
  id: string;
}

interface AuthPayload {
  userId: string;
  token: string;
}

interface MessagePayload {
  sessionId: string;
  message: Message;
}

interface Connection {
  ws: WebSocket;
  userId: string;
  isAlive: boolean;
}

export class RealtimeServer {
  private wss: WebSocketServer;
  private connections: Map<string, Connection> = new Map();
  private userConnections: Map<string, Set<string>> = new Map();

  constructor(port: number = 8080) {
    const app = express();
    app.use(express.json());

    // Health check endpoint
    app.get('/health', (req, res) => {
      res.json({ 
        status: 'healthy', 
        connections: this.connections.size,
        uptime: process.uptime()
      });
    });

    // REST API endpoints
    app.post('/api/messages', this.handleRestMessage.bind(this));
    app.get('/api/sessions/:sessionId/messages', this.getMessages.bind(this));

    const server = createServer(app);
    
    this.wss = new WebSocketServer({ 
      server,
      path: '/ws'
    });

    this.setupWebSocketServer();
    
    server.listen(port, () => {
      console.log(`E2E Chat Server running on port ${port}`);
    });

    // Setup heartbeat
    this.setupHeartbeat();
  }

  private setupWebSocketServer(): void {
    this.wss.on('connection', (ws: WebSocket) => {
      const connectionId = uuidv4();
      console.log(`New connection: ${connectionId}`);

      ws.on('message', async (data: Buffer) => {
        try {
          const message: WSMessage = JSON.parse(data.toString());
          await this.handleMessage(connectionId, ws, message);
        } catch (error) {
          console.error('Error handling message:', error);
          this.sendError(ws, 'Invalid message format');
        }
      });

      ws.on('close', () => {
        this.handleDisconnect(connectionId);
      });

      ws.on('error', (error) => {
        console.error(`WebSocket error for ${connectionId}:`, error);
      });

      ws.on('pong', () => {
        const connection = this.connections.get(connectionId);
        if (connection) {
          connection.isAlive = true;
        }
      });
    });
  }

  private async handleMessage(
    connectionId: string,
    ws: WebSocket,
    message: WSMessage
  ): Promise<void> {
    switch (message.type) {
      case 'auth':
        await this.handleAuth(connectionId, ws, message.payload as AuthPayload);
        break;
      
      case 'message':
        await this.handleChatMessage(connectionId, message.payload as MessagePayload);
        break;
      
      case 'typing':
        await this.handleTypingIndicator(connectionId, message.payload);
        break;
      
      case 'read':
        await this.handleReadReceipt(connectionId, message.payload);
        break;
      
      case 'presence':
        await this.handlePresence(connectionId, message.payload);
        break;
      
      case 'key_exchange':
        await this.handleKeyExchange(connectionId, message.payload);
        break;
      
      default:
        this.sendError(ws, `Unknown message type: ${message.type}`);
    }
  }

  private async handleAuth(
    connectionId: string,
    ws: WebSocket,
    payload: AuthPayload
  ): Promise<void> {
    // Validate token (simplified for demo)
    if (!payload.token) {
      this.sendError(ws, 'Authentication failed');
      ws.close();
      return;
    }

    // Store connection
    const connection: Connection = {
      ws,
      userId: payload.userId,
      isAlive: true
    };
    
    this.connections.set(connectionId, connection);
    
    // Track user connections
    if (!this.userConnections.has(payload.userId)) {
      this.userConnections.set(payload.userId, new Set());
    }
    this.userConnections.get(payload.userId)!.add(connectionId);

    // Send success response
    this.sendMessage(ws, {
      type: 'auth',
      payload: { success: true, userId: payload.userId },
      id: uuidv4()
    });

    // Notify presence
    this.broadcastPresence(payload.userId, 'online');
  }

  private async handleChatMessage(
    connectionId: string,
    payload: MessagePayload
  ): Promise<void> {
    const connection = this.connections.get(connectionId);
    if (!connection) {
      return;
    }

    // Forward encrypted message to recipient
    const recipientId = payload.message.recipientId;
    const recipientConnections = this.userConnections.get(recipientId);
    
    if (recipientConnections) {
      for (const recipientConnectionId of recipientConnections) {
        const recipientConnection = this.connections.get(recipientConnectionId);
        if (recipientConnection) {
          this.sendMessage(recipientConnection.ws, {
            type: 'message',
            payload: payload,
            id: uuidv4()
          });
        }
      }
      
      // Update message status to delivered
      payload.message.status = 'delivered';
    }

    // Send acknowledgment to sender
    this.sendMessage(connection.ws, {
      type: 'message_ack',
      payload: {
        messageId: payload.message.id,
        status: payload.message.status
      },
      id: uuidv4()
    });
  }

  private async handleTypingIndicator(
    connectionId: string,
    payload: any
  ): Promise<void> {
    const connection = this.connections.get(connectionId);
    if (!connection) return;

    const recipientConnections = this.userConnections.get(payload.recipientId);
    if (recipientConnections) {
      for (const recipientConnectionId of recipientConnections) {
        const recipientConnection = this.connections.get(recipientConnectionId);
        if (recipientConnection) {
          this.sendMessage(recipientConnection.ws, {
            type: 'typing',
            payload: {
              userId: connection.userId,
              isTyping: payload.isTyping
            },
            id: uuidv4()
          });
        }
      }
    }
  }

  private async handleReadReceipt(
    connectionId: string,
    payload: any
  ): Promise<void> {
    const connection = this.connections.get(connectionId);
    if (!connection) return;

    // Forward read receipt to sender
    const senderConnections = this.userConnections.get(payload.senderId);
    if (senderConnections) {
      for (const senderConnectionId of senderConnections) {
        const senderConnection = this.connections.get(senderConnectionId);
        if (senderConnection) {
          this.sendMessage(senderConnection.ws, {
            type: 'read',
            payload: {
              messageId: payload.messageId,
              readBy: connection.userId,
              readAt: new Date()
            },
            id: uuidv4()
          });
        }
      }
    }
  }

  private async handlePresence(
    connectionId: string,
    payload: any
  ): Promise<void> {
    const connection = this.connections.get(connectionId);
    if (!connection) return;

    this.broadcastPresence(connection.userId, payload.status);
  }

  private async handleKeyExchange(
    connectionId: string,
    payload: any
  ): Promise<void> {
    const connection = this.connections.get(connectionId);
    if (!connection) return;

    // Forward key exchange data to recipient
    const recipientConnections = this.userConnections.get(payload.recipientId);
    if (recipientConnections) {
      for (const recipientConnectionId of recipientConnections) {
        const recipientConnection = this.connections.get(recipientConnectionId);
        if (recipientConnection) {
          this.sendMessage(recipientConnection.ws, {
            type: 'key_exchange',
            payload: {
              senderId: connection.userId,
              keyData: payload.keyData
            },
            id: uuidv4()
          });
        }
      }
    }
  }

  private handleDisconnect(connectionId: string): void {
    const connection = this.connections.get(connectionId);
    if (connection) {
      // Remove from user connections
      const userConnections = this.userConnections.get(connection.userId);
      if (userConnections) {
        userConnections.delete(connectionId);
        if (userConnections.size === 0) {
          this.userConnections.delete(connection.userId);
          // User is completely offline
          this.broadcastPresence(connection.userId, 'offline');
        }
      }
      
      this.connections.delete(connectionId);
    }
    
    console.log(`Connection closed: ${connectionId}`);
  }

  private broadcastPresence(userId: string, status: string): void {
    // Broadcast presence update to all connected users
    for (const [, connection] of this.connections) {
      this.sendMessage(connection.ws, {
        type: 'presence',
        payload: {
          userId,
          status,
          timestamp: new Date()
        },
        id: uuidv4()
      });
    }
  }

  private sendMessage(ws: WebSocket, message: WSMessage): void {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify(message));
    }
  }

  private sendError(ws: WebSocket, error: string): void {
    this.sendMessage(ws, {
      type: 'error',
      payload: { error },
      id: uuidv4()
    });
  }

  private setupHeartbeat(): void {
    const interval = setInterval(() => {
      for (const [connectionId, connection] of this.connections) {
        if (!connection.isAlive) {
          connection.ws.terminate();
          this.handleDisconnect(connectionId);
        } else {
          connection.isAlive = false;
          connection.ws.ping();
        }
      }
    }, 30000); // 30 seconds

    this.wss.on('close', () => {
      clearInterval(interval);
    });
  }

  // REST API handlers
  private async handleRestMessage(req: any, res: any): Promise<void> {
    try {
      const message = req.body as Message;
      
      // Store message (would be saved to database)
      // Forward via WebSocket if recipient is online
      const recipientConnections = this.userConnections.get(message.recipientId);
      if (recipientConnections && recipientConnections.size > 0) {
        for (const connectionId of recipientConnections) {
          const connection = this.connections.get(connectionId);
          if (connection) {
            this.sendMessage(connection.ws, {
              type: 'message',
              payload: { message },
              id: uuidv4()
            });
          }
        }
        message.status = 'delivered';
      } else {
        message.status = 'sent';
      }
      
      res.json({ success: true, message });
    } catch (error) {
      res.status(500).json({ error: 'Failed to send message' });
    }
  }

  private async getMessages(req: any, res: any): Promise<void> {
    try {
      const { sessionId } = req.params;
      // Would fetch from database
      res.json({ messages: [] });
    } catch (error) {
      res.status(500).json({ error: 'Failed to fetch messages' });
    }
  }
}