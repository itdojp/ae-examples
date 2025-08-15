import { FastifyInstance, FastifyRequest, FastifyReply } from 'fastify';
import { 
  RegisterUserRequest,
  LoginRequest,
  RefreshTokenRequest,
  Enable2FARequest,
  Verify2FARequest,
  UserResponse,
  AuthTokenResponse,
  TwoFactorSetupResponse,
  ErrorResponse
} from '../../domain/contracts';
import { AuthServiceImpl } from '../../domain/services/authService';
import { KeyServiceImpl } from '../../domain/services/keyService';
import { UserRepositoryImpl } from '../../infra/repositories/userRepository';
import { KeyRepositoryImpl } from '../../infra/repositories/keyRepository';
import { Database } from '../../infra/db';
import QRCode from 'qrcode';

export async function authRoutes(fastify: FastifyInstance) {
  const db = new Database(process.env.DATABASE_URL || 'postgresql://localhost/e2echat');
  const userRepository = new UserRepositoryImpl(db);
  const keyRepository = new KeyRepositoryImpl(db);
  const keyService = new KeyServiceImpl(db, keyRepository);
  const authService = new AuthServiceImpl(db, userRepository, keyService);

  // Register user
  fastify.post<{
    Body: RegisterUserRequest
  }>('/auth/register', {
    schema: {
      body: RegisterUserRequest,
      response: {
        201: UserResponse,
        400: ErrorResponse,
        409: ErrorResponse
      }
    }
  }, async (request: FastifyRequest<{ Body: RegisterUserRequest }>, reply: FastifyReply) => {
    try {
      const { email, password, displayName } = request.body;
      
      const user = await authService.register(email, password, displayName);
      
      reply.code(201).send({
        id: user.id,
        email: user.email,
        displayName: user.displayName,
        isVerified: user.isVerified,
        createdAt: user.createdAt.toISOString(),
        lastSeen: user.lastSeen?.toISOString()
      });
    } catch (error: any) {
      if (error.message === 'Email already registered') {
        reply.code(409).send({
          error: 'CONFLICT',
          message: error.message
        });
      } else {
        reply.code(400).send({
          error: 'BAD_REQUEST',
          message: error.message
        });
      }
    }
  });

  // Login
  fastify.post<{
    Body: LoginRequest
  }>('/auth/login', {
    schema: {
      body: LoginRequest,
      response: {
        200: AuthTokenResponse,
        401: ErrorResponse,
        403: ErrorResponse
      }
    }
  }, async (request: FastifyRequest<{ Body: LoginRequest }>, reply: FastifyReply) => {
    try {
      const { email, password, deviceFingerprint, totpCode } = request.body;
      
      const authToken = await authService.login(email, password, deviceFingerprint, totpCode);
      
      reply.send({
        token: authToken.token,
        refreshToken: authToken.refreshToken,
        expiresIn: 3600,
        tokenType: 'Bearer' as const
      });
    } catch (error: any) {
      if (error.message === '2FA code required') {
        reply.code(403).send({
          error: '2FA_REQUIRED',
          message: error.message
        });
      } else if (error.message === 'Invalid 2FA code') {
        reply.code(403).send({
          error: 'INVALID_2FA',
          message: error.message
        });
      } else {
        reply.code(401).send({
          error: 'UNAUTHORIZED',
          message: 'Invalid credentials'
        });
      }
    }
  });

  // Logout
  fastify.post('/auth/logout', {
    preHandler: async (request, reply) => {
      // Verify JWT token
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
      
      request.user = user;
      request.token = token;
    }
  }, async (request: any, reply: FastifyReply) => {
    await authService.logout(request.token);
    reply.code(204).send();
  });

  // Refresh token
  fastify.post<{
    Body: RefreshTokenRequest
  }>('/auth/refresh', {
    schema: {
      body: RefreshTokenRequest,
      response: {
        200: AuthTokenResponse,
        401: ErrorResponse
      }
    }
  }, async (request: FastifyRequest<{ Body: RefreshTokenRequest }>, reply: FastifyReply) => {
    try {
      const { refreshToken } = request.body;
      
      const authToken = await authService.refreshToken(refreshToken);
      
      reply.send({
        token: authToken.token,
        refreshToken: authToken.refreshToken,
        expiresIn: 3600,
        tokenType: 'Bearer' as const
      });
    } catch (error: any) {
      reply.code(401).send({
        error: 'UNAUTHORIZED',
        message: error.message
      });
    }
  });

  // Enable 2FA
  fastify.post('/auth/2fa/enable', {
    preHandler: async (request, reply) => {
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
      
      request.user = user;
    },
    schema: {
      response: {
        200: TwoFactorSetupResponse,
        401: ErrorResponse
      }
    }
  }, async (request: any, reply: FastifyReply) => {
    const twoFA = await authService.enable2FA(request.user.id);
    
    // Generate QR code
    const otpAuthUrl = `otpauth://totp/E2E%20Chat:${request.user.email}?secret=${twoFA.secret}&issuer=E2E%20Chat`;
    const qrCode = await QRCode.toDataURL(otpAuthUrl);
    
    reply.send({
      secret: twoFA.secret,
      qrCode,
      backupCodes: twoFA.backupCodes
    });
  });

  // Verify 2FA
  fastify.post<{
    Body: Verify2FARequest
  }>('/auth/2fa/verify', {
    preHandler: async (request, reply) => {
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
      
      request.user = user;
    },
    schema: {
      body: Verify2FARequest
    }
  }, async (request: FastifyRequest<{ Body: Verify2FARequest }> & any, reply: FastifyReply) => {
    const { code } = request.body;
    
    const isValid = await authService.verify2FA(request.user.id, code);
    
    if (isValid) {
      reply.send({ success: true });
    } else {
      reply.code(400).send({
        error: 'INVALID_CODE',
        message: 'Invalid 2FA code'
      });
    }
  });
}