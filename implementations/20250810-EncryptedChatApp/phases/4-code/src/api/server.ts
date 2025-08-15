import Fastify from 'fastify';
import { WebSocketServer } from 'ws';
import { authRoutes } from './routes/auth';
import { keyRoutes } from './routes/keys';
import { messageRoutes } from './routes/messages';
import { WebSocketMessage } from '../domain/contracts';
import jwt from 'jsonwebtoken';

const app = Fastify({ 
  logger: {
    level: process.env.LOG_LEVEL || 'info',
    transport: {
      target: 'pino-pretty',
      options: {
        colorize: true
      }
    }
  }
});

// Register CORS
app.register(import('@fastify/cors'), {
  origin: process.env.CORS_ORIGIN || '*',
  credentials: true
});

// Register Swagger for API documentation
app.register(import('@fastify/swagger'), {
  openapi: {
    info: {
      title: 'E2E Encrypted Chat API',
      description: 'End-to-end encrypted messaging API with Signal Protocol',
      version: '1.0.0'
    },
    servers: [
      {
        url: process.env.API_URL || 'http://localhost:3000',
        description: 'Development server'
      }
    ],
    components: {
      securitySchemes: {
        bearerAuth: {
          type: 'http',
          scheme: 'bearer',
          bearerFormat: 'JWT'
        }
      }
    },
    security: [{ bearerAuth: [] }]
  }
});

// Register Swagger UI
app.register(import('@fastify/swagger-ui'), {
  routePrefix: '/docs',
  uiConfig: {
    docExpansion: 'list',
    deepLinking: false
  }
});

// Health check endpoint
app.get('/health', async (request, reply) => {
  return { status: 'healthy', timestamp: new Date().toISOString() };
});

// Register route modules
app.register(authRoutes);
app.register(keyRoutes);
app.register(messageRoutes);

// WebSocket server for real-time messaging
const wss = new WebSocketServer({ noServer: true });
const clients = new Map<string, any>();

wss.on('connection', (ws, request) => {
  let userId: string | null = null;
  
  // Authenticate WebSocket connection
  ws.on('message', async (data) => {
    try {
      const message = JSON.parse(data.toString());
      
      // First message should be authentication
      if (!userId && message.type === 'auth') {
        const token = message.token;
        const jwtSecret = process.env.JWT_SECRET || 'development-secret-change-in-production';
        
        try {
          const decoded = jwt.verify(token, jwtSecret) as any;
          userId = decoded.userId;
          clients.set(userId, ws);
          
          ws.send(JSON.stringify({
            type: 'auth',
            payload: { success: true, userId }
          }));
        } catch (error) {
          ws.send(JSON.stringify({
            type: 'auth',
            payload: { success: false, error: 'Invalid token' }
          }));
          ws.close();
        }
      } else if (userId) {
        // Handle other message types
        const parsed = WebSocketMessage.safeParse(message);
        if (!parsed.success) {
          ws.send(JSON.stringify({
            type: 'error',
            payload: { error: 'Invalid message format' }
          }));
          return;
        }
        
        const wsMessage = parsed.data;
        
        switch (wsMessage.type) {
          case 'message':
            // Forward message to recipient if online
            const recipientWs = clients.get(wsMessage.payload.recipientId);
            if (recipientWs && recipientWs.readyState === ws.OPEN) {
              recipientWs.send(JSON.stringify(wsMessage));
            }
            break;
            
          case 'receipt':
            // Forward receipt to sender
            // Get sender ID from message in database
            // const senderWs = clients.get(senderId);
            // if (senderWs) senderWs.send(JSON.stringify(wsMessage));
            break;
            
          case 'typing':
            // Forward typing indicator
            const typingRecipient = clients.get(wsMessage.payload.userId);
            if (typingRecipient && typingRecipient.readyState === ws.OPEN) {
              typingRecipient.send(JSON.stringify(wsMessage));
            }
            break;
            
          case 'presence':
            // Broadcast presence update to contacts
            // TODO: Get user's contacts and notify them
            break;
        }
      }
    } catch (error) {
      app.log.error('WebSocket message error:', error);
      ws.send(JSON.stringify({
        type: 'error',
        payload: { error: 'Message processing failed' }
      }));
    }
  });
  
  ws.on('close', () => {
    if (userId) {
      clients.delete(userId);
      // Broadcast offline presence
      // TODO: Notify contacts
    }
  });
  
  ws.on('error', (error) => {
    app.log.error('WebSocket error:', error);
  });
});

// Upgrade HTTP to WebSocket
app.server.on('upgrade', (request, socket, head) => {
  if (request.url === '/ws') {
    wss.handleUpgrade(request, socket, head, (ws) => {
      wss.emit('connection', ws, request);
    });
  } else {
    socket.destroy();
  }
});

// Error handler
app.setErrorHandler((error, request, reply) => {
  app.log.error(error);
  
  if (error.validation) {
    reply.status(400).send({
      error: 'VALIDATION_ERROR',
      message: 'Request validation failed',
      details: error.validation
    });
  } else if (error.statusCode) {
    reply.status(error.statusCode).send({
      error: error.code || 'ERROR',
      message: error.message
    });
  } else {
    reply.status(500).send({
      error: 'INTERNAL_SERVER_ERROR',
      message: 'An unexpected error occurred'
    });
  }
});

// Graceful shutdown
const gracefulShutdown = async () => {
  app.log.info('Shutting down gracefully...');
  
  // Close WebSocket connections
  wss.clients.forEach((ws) => {
    ws.close();
  });
  
  await app.close();
  process.exit(0);
};

process.on('SIGTERM', gracefulShutdown);
process.on('SIGINT', gracefulShutdown);

export default app;