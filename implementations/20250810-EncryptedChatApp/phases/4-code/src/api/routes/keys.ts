import { FastifyInstance, FastifyRequest, FastifyReply } from 'fastify';
import { 
  KeyBundle,
  UploadKeysRequest,
  RotateSignedPreKeyRequest,
  ErrorResponse
} from '../../domain/contracts';
import { KeyServiceImpl } from '../../domain/services/keyService';
import { AuthServiceImpl } from '../../domain/services/authService';
import { KeyRepositoryImpl } from '../../infra/repositories/keyRepository';
import { UserRepositoryImpl } from '../../infra/repositories/userRepository';
import { Database } from '../../infra/db';

export async function keyRoutes(fastify: FastifyInstance) {
  const db = new Database(process.env.DATABASE_URL || 'postgresql://localhost/e2echat');
  const keyRepository = new KeyRepositoryImpl(db);
  const userRepository = new UserRepositoryImpl(db);
  const keyService = new KeyServiceImpl(db, keyRepository);
  const authService = new AuthServiceImpl(db, userRepository, keyService);

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

  // Get user's public key bundle
  fastify.get<{
    Params: { userId: string }
  }>('/keys/bundle/:userId', {
    schema: {
      params: {
        type: 'object',
        properties: {
          userId: { type: 'string', format: 'uuid' }
        },
        required: ['userId']
      },
      response: {
        200: KeyBundle,
        404: ErrorResponse
      }
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Params: { userId: string } }>, reply: FastifyReply) => {
    try {
      const { userId } = request.params;
      
      const keyBundle = await keyService.getPublicKeyBundle(userId);
      
      reply.send(keyBundle);
    } catch (error: any) {
      if (error.message === 'User keys not found') {
        reply.code(404).send({
          error: 'NOT_FOUND',
          message: error.message
        });
      } else {
        reply.code(500).send({
          error: 'INTERNAL_ERROR',
          message: 'Failed to retrieve key bundle'
        });
      }
    }
  });

  // Upload user keys
  fastify.post<{
    Body: UploadKeysRequest
  }>('/keys/upload', {
    schema: {
      body: UploadKeysRequest
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Body: UploadKeysRequest }> & any, reply: FastifyReply) => {
    try {
      const { identityKey, signedPreKey, oneTimePreKeys } = request.body;
      const userId = request.user.id;
      
      // Validate and save keys
      await db.transaction(async (client) => {
        // Save identity key
        await client.query(
          `INSERT INTO identity_keys (user_id, public_key, created_at)
           VALUES ($1, $2, NOW())
           ON CONFLICT (user_id) DO UPDATE SET public_key = $2`,
          [userId, identityKey]
        );
        
        // Save signed pre-key
        await client.query(
          `INSERT INTO signed_pre_keys (user_id, key_id, public_key, signature, created_at, expires_at)
           VALUES ($1, $2, $3, $4, NOW(), NOW() + INTERVAL '30 days')
           ON CONFLICT (user_id, key_id) DO UPDATE 
           SET public_key = $3, signature = $4, expires_at = NOW() + INTERVAL '30 days'`,
          [userId, signedPreKey.id, signedPreKey.key, signedPreKey.signature]
        );
        
        // Save one-time pre-keys
        for (const otpk of oneTimePreKeys) {
          await client.query(
            `INSERT INTO one_time_pre_keys (user_id, key_id, public_key, used, created_at)
             VALUES ($1, $2, $3, false, NOW())
             ON CONFLICT (user_id, key_id) DO NOTHING`,
            [userId, otpk.id, otpk.key]
          );
        }
      });
      
      reply.code(204).send();
    } catch (error: any) {
      reply.code(400).send({
        error: 'BAD_REQUEST',
        message: 'Failed to upload keys'
      });
    }
  });

  // Rotate signed pre-key
  fastify.post<{
    Body: RotateSignedPreKeyRequest
  }>('/keys/rotate/signed', {
    schema: {
      body: RotateSignedPreKeyRequest
    },
    preHandler: authenticate
  }, async (request: FastifyRequest<{ Body: RotateSignedPreKeyRequest }> & any, reply: FastifyReply) => {
    try {
      const { signedPreKey } = request.body;
      const userId = request.user.id;
      
      // Save new signed pre-key and mark old ones for expiration
      await db.transaction(async (client) => {
        // Mark current keys as expiring in 5 days
        await client.query(
          `UPDATE signed_pre_keys 
           SET expires_at = NOW() + INTERVAL '5 days'
           WHERE user_id = $1 AND expires_at > NOW()`,
          [userId]
        );
        
        // Insert new key
        await client.query(
          `INSERT INTO signed_pre_keys (user_id, key_id, public_key, signature, created_at, expires_at)
           VALUES ($1, $2, $3, $4, NOW(), NOW() + INTERVAL '30 days')`,
          [userId, signedPreKey.id, signedPreKey.key, signedPreKey.signature]
        );
      });
      
      reply.code(204).send();
    } catch (error: any) {
      reply.code(400).send({
        error: 'BAD_REQUEST',
        message: 'Failed to rotate key'
      });
    }
  });

  // Replenish one-time pre-keys
  fastify.post('/keys/replenish', {
    preHandler: authenticate
  }, async (request: any, reply: FastifyReply) => {
    try {
      const userId = request.user.id;
      
      // Count unused keys
      const countResult = await db.query(
        'SELECT COUNT(*) as count FROM one_time_pre_keys WHERE user_id = $1 AND used = false',
        [userId]
      );
      
      const unusedCount = parseInt(countResult.rows[0].count, 10);
      
      if (unusedCount < 10) {
        // Generate more keys
        const newCount = 100 - unusedCount;
        await keyService.generateOneTimePreKeys(userId, newCount);
      }
      
      reply.send({ 
        message: 'Keys replenished',
        currentCount: Math.max(100, unusedCount)
      });
    } catch (error: any) {
      reply.code(500).send({
        error: 'INTERNAL_ERROR',
        message: 'Failed to replenish keys'
      });
    }
  });

  // Get key statistics (for monitoring)
  fastify.get('/keys/stats', {
    preHandler: authenticate
  }, async (request: any, reply: FastifyReply) => {
    try {
      const userId = request.user.id;
      
      // Get key counts
      const [identityResult, signedResult, oneTimeResult] = await Promise.all([
        db.query('SELECT COUNT(*) as count FROM identity_keys WHERE user_id = $1', [userId]),
        db.query('SELECT COUNT(*) as count FROM signed_pre_keys WHERE user_id = $1 AND expires_at > NOW()', [userId]),
        db.query('SELECT COUNT(*) as count FROM one_time_pre_keys WHERE user_id = $1 AND used = false', [userId])
      ]);
      
      reply.send({
        identityKeys: parseInt(identityResult.rows[0].count, 10),
        activeSignedPreKeys: parseInt(signedResult.rows[0].count, 10),
        unusedOneTimePreKeys: parseInt(oneTimeResult.rows[0].count, 10)
      });
    } catch (error: any) {
      reply.code(500).send({
        error: 'INTERNAL_ERROR',
        message: 'Failed to get key statistics'
      });
    }
  });
}