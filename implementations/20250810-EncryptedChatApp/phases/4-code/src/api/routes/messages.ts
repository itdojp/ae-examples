import { FastifyInstance, FastifyRequest, FastifyReply } from 'fastify';
import { 
  SendMessageRequest,
  GetMessagesRequest,
  MessageReceiptRequest,
  MessageResponse,
  MessagesListResponse,
  ErrorResponse,
  EstablishSessionRequest,
  SessionResponse,
  SafetyNumberResponse
} from '../../domain/contracts';
import { MessageServiceImpl } from '../../domain/services/messageService';
import { SessionServiceImpl } from '../../domain/services/sessionService';
import { AuthServiceImpl } from '../../domain/services/authService';
import { MessageRepositoryImpl } from '../../infra/repositories/messageRepository';
import { SessionRepositoryImpl } from '../../infra/repositories/sessionRepository';
import { KeyRepositoryImpl } from '../../infra/repositories/keyRepository';
import { UserRepositoryImpl } from '../../infra/repositories/userRepository';
import { Database } from '../../infra/db';
import { KeyManager } from '../../domain/crypto/keyManager';
import QRCode from 'qrcode';

export async function messageRoutes(fastify: FastifyInstance) {
  const db = new Database(process.env.DATABASE_URL || 'postgresql://localhost/e2echat');
  const messageRepository = new MessageRepositoryImpl(db);
  const sessionRepository = new SessionRepositoryImpl(db);
  const keyRepository = new KeyRepositoryImpl(db);
  const userRepository = new UserRepositoryImpl(db);
  const sessionService = new SessionServiceImpl(db, sessionRepository, keyRepository);
  const messageService = new MessageServiceImpl(db, sessionService, messageRepository, sessionRepository);
  const keyService = new (await import('../../domain/services/keyService')).KeyServiceImpl(db, keyRepository);
  const authService = new AuthServiceImpl(db, userRepository, keyService);
  const keyManager = await KeyManager.getInstance();

  // Middleware to verify authentication
  const authenticate = async (request: FastifyRequest, reply: FastifyReply) => {
    const token = request.headers.authorization?.replace('Bearer ', '');
    if (!token) {
      reply.code(401).send({ error: 'UNAUTHORIZED', message: 'Token required' });
      return;
    }
    
    const user = await authService.verifyToken(token);
    if (!user) {
      reply.code(401).send({ error: 'UNAUTHORIZED', message: 'Invalid token' });
      return;
    }
    
    (request as any).user = user;
  };

  // Send encrypted message
  fastify.post<{
    Body: SendMessageRequest
  }>('/messages/send', {
    schema: {
      body: SendMessageRequest,
      response: {
        201: MessageResponse,
        400: ErrorResponse,
        404: ErrorResponse
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Body: SendMessageRequest }> & any, reply: FastifyReply) => {
    try {
      const userId = request.user.id;
      const { recipientId, ciphertext, nonce, authTag, dhPublicKey, messageNumber, previousChainLength } = request.body;
      
      // For simplicity, we'll use the service to handle the encryption
      // In a real implementation, the client would encrypt and send the ciphertext
      const message = await messageService.sendMessage(userId, recipientId, ciphertext);
      
      reply.code(201).send({
        id: message.id,
        senderId: message.senderId,
        recipientId: message.recipientId,
        ciphertext: message.ciphertext,
        nonce: message.nonce,
        authTag: message.authTag,
        timestamp: message.timestamp.toISOString(),
        delivered: message.delivered,
        read: message.read
      });
    } catch (error: any) {
      if (error.message.includes('not found')) {
        reply.code(404).send({
          error: 'NOT_FOUND',
          message: 'Recipient not found'
        });
      } else {
        reply.code(400).send({
          error: 'BAD_REQUEST',
          message: error.message
        });
      }
    }
  });

  // Get messages with a user
  fastify.get<{
    Params: { userId: string },
    Querystring: GetMessagesRequest
  }>('/messages/:userId', {
    schema: {
      params: {
        type: 'object',
        properties: {
          userId: { type: 'string', format: 'uuid' }
        },
        required: ['userId']
      },
      querystring: GetMessagesRequest,
      response: {
        200: MessagesListResponse
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { userId: string }, Querystring: GetMessagesRequest }> & any, reply: FastifyReply) => {
    const currentUserId = request.user.id;
    const { userId: peerId } = request.params;
    const { limit = 50, offset = 0 } = request.query;
    
    const messages = await messageService.getMessages(currentUserId, peerId, limit, offset);
    
    reply.send({
      messages: messages.map(msg => ({
        id: msg.id,
        senderId: msg.senderId,
        recipientId: msg.recipientId,
        ciphertext: msg.ciphertext,
        nonce: msg.nonce,
        authTag: msg.authTag,
        timestamp: msg.timestamp.toISOString(),
        delivered: msg.delivered,
        read: msg.read
      })),
      total: messages.length,
      hasMore: messages.length === limit
    });
  });

  // Send message receipt
  fastify.post<{
    Params: { messageId: string },
    Body: MessageReceiptRequest
  }>('/messages/:messageId/receipt', {
    schema: {
      params: {
        type: 'object',
        properties: {
          messageId: { type: 'string', format: 'uuid' }
        },
        required: ['messageId']
      },
      body: MessageReceiptRequest
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { messageId: string }, Body: MessageReceiptRequest }> & any, reply: FastifyReply) => {
    try {
      const { messageId } = request.params;
      const { status } = request.body;
      const userId = request.user.id;
      
      if (status === 'delivered') {
        await messageService.markAsDelivered(messageId);
      } else if (status === 'read') {
        await messageService.markAsRead(messageId);
      }
      
      // Save receipt
      await messageRepository.saveReceipt({
        id: '',
        messageId,
        recipientId: userId,
        status,
        timestamp: new Date()
      });
      
      reply.code(204).send();
    } catch (error: any) {
      reply.code(404).send({
        error: 'NOT_FOUND',
        message: 'Message not found'
      });
    }
  });

  // Establish session with user
  fastify.post<{
    Params: { userId: string },
    Body: EstablishSessionRequest
  }>('/sessions/:userId', {
    schema: {
      params: {
        type: 'object',
        properties: {
          userId: { type: 'string', format: 'uuid' }
        },
        required: ['userId']
      },
      body: EstablishSessionRequest,
      response: {
        201: SessionResponse,
        400: ErrorResponse
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { userId: string }, Body: EstablishSessionRequest }> & any, reply: FastifyReply) => {
    try {
      const currentUserId = request.user.id;
      const { userId: peerId } = request.params;
      
      const session = await sessionService.establishSession(currentUserId, peerId);
      
      reply.code(201).send({
        id: session.id,
        userId: session.userId,
        peerId: session.peerId,
        established: true,
        createdAt: session.createdAt.toISOString()
      });
    } catch (error: any) {
      reply.code(400).send({
        error: 'BAD_REQUEST',
        message: error.message
      });
    }
  });

  // Get safety number for verification
  fastify.get<{
    Params: { userId: string }
  }>('/verification/:userId/safety-number', {
    schema: {
      params: {
        type: 'object',
        properties: {
          userId: { type: 'string', format: 'uuid' }
        },
        required: ['userId']
      },
      response: {
        200: SafetyNumberResponse,
        404: ErrorResponse
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { userId: string } }> & any, reply: FastifyReply) => {
    try {
      const currentUserId = request.user.id;
      const { userId: peerId } = request.params;
      
      // Get identity keys for both users
      const [currentUserKey, peerKey] = await Promise.all([
        keyRepository.getIdentityKey(currentUserId),
        keyRepository.getIdentityKey(peerId)
      ]);
      
      if (!currentUserKey || !peerKey) {
        reply.code(404).send({
          error: 'NOT_FOUND',
          message: 'User keys not found'
        });
        return;
      }
      
      const safetyNumber = keyManager.generateSafetyNumber(
        currentUserKey.publicKey,
        peerKey.publicKey
      );
      
      // Generate QR code
      const qrData = `VERIFY:${currentUserId}:${peerId}:${safetyNumber}`;
      const qrCode = await QRCode.toDataURL(qrData);
      
      reply.send({
        safetyNumber,
        qrCode
      });
    } catch (error: any) {
      reply.code(404).send({
        error: 'NOT_FOUND',
        message: 'User not found'
      });
    }
  });

  // Mark user as verified
  fastify.post<{
    Params: { userId: string }
  }>('/verification/:userId/verify', {
    schema: {
      params: {
        type: 'object',
        properties: {
          userId: { type: 'string', format: 'uuid' }
        },
        required: ['userId']
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { userId: string } }> & any, reply: FastifyReply) => {
    try {
      const currentUserId = request.user.id;
      const { userId: peerId } = request.params;
      
      // Save verification status
      await db.query(
        `INSERT INTO safety_numbers (user_id_1, user_id_2, number, qr_code, verified, verified_at, created_at)
         VALUES ($1, $2, '', '', true, NOW(), NOW())
         ON CONFLICT (user_id_1, user_id_2) DO UPDATE 
         SET verified = true, verified_at = NOW()`,
        [currentUserId < peerId ? currentUserId : peerId, 
         currentUserId < peerId ? peerId : currentUserId]
      );
      
      reply.code(204).send();
    } catch (error: any) {
      reply.code(404).send({
        error: 'NOT_FOUND',
        message: 'User not found'
      });
    }
  });
}