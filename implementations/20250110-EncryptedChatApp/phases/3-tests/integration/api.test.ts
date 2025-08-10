import { describe, it, expect, beforeAll, afterAll, beforeEach } from 'vitest';
import { FastifyInstance } from 'fastify';
import { Database } from '../../src/infra/db';
import app from '../../src/api/server';

describe('API Integration Tests', () => {
  let server: FastifyInstance;
  let db: Database;
  let authToken: string;
  let userId: string;

  beforeAll(async () => {
    // Initialize database
    db = new Database(process.env.DATABASE_URL || 'postgresql://app:app@localhost:5432/e2echat_test');
    
    // Start server
    server = app;
    await server.ready();
  });

  afterAll(async () => {
    await server.close();
    await db.close();
  });

  beforeEach(async () => {
    // Clean database
    await db.query('TRUNCATE TABLE users, devices, identity_keys, signed_pre_keys, one_time_pre_keys, sessions, messages CASCADE');
  });

  describe('Authentication Flow', () => {
    it('should register a new user', async () => {
      const response = await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'Test User'
        }
      });

      expect(response.statusCode).toBe(201);
      const body = JSON.parse(response.body);
      expect(body.email).toBe('test@example.com');
      expect(body.displayName).toBe('Test User');
      expect(body.id).toBeDefined();
      userId = body.id;
    });

    it('should login with valid credentials', async () => {
      // First register
      await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'Test User'
        }
      });

      // Then login
      const response = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          deviceFingerprint: 'test-device-123'
        }
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.token).toBeDefined();
      expect(body.tokenType).toBe('Bearer');
      authToken = body.token;
    });

    it('should reject invalid credentials', async () => {
      const response = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'nonexistent@example.com',
          password: 'WrongPassword',
          deviceFingerprint: 'test-device'
        }
      });

      expect(response.statusCode).toBe(401);
    });

    it('should enable 2FA', async () => {
      // Register and login first
      await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'Test User'
        }
      });

      const loginResponse = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          deviceFingerprint: 'test-device'
        }
      });

      const { token } = JSON.parse(loginResponse.body);

      // Enable 2FA
      const response = await server.inject({
        method: 'POST',
        url: '/auth/2fa/enable',
        headers: {
          Authorization: `Bearer ${token}`
        }
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.secret).toBeDefined();
      expect(body.qrCode).toBeDefined();
      expect(body.backupCodes).toBeInstanceOf(Array);
    });
  });

  describe('Key Management', () => {
    beforeEach(async () => {
      // Setup authenticated user
      const registerResponse = await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'Test User'
        }
      });
      userId = JSON.parse(registerResponse.body).id;

      const loginResponse = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecureP@ssw0rd123',
          deviceFingerprint: 'test-device'
        }
      });
      authToken = JSON.parse(loginResponse.body).token;
    });

    it('should upload cryptographic keys', async () => {
      const response = await server.inject({
        method: 'POST',
        url: '/keys/upload',
        headers: {
          Authorization: `Bearer ${authToken}`
        },
        payload: {
          identityKey: {
            publicKey: 'test-identity-public-key',
            privateKey: 'test-identity-private-key'
          },
          signedPreKey: {
            id: 1,
            publicKey: 'test-signed-public-key',
            privateKey: 'test-signed-private-key',
            signature: 'test-signature'
          },
          oneTimePreKeys: [
            {
              id: 1,
              publicKey: 'test-onetime-public-1',
              privateKey: 'test-onetime-private-1'
            }
          ]
        }
      });

      expect(response.statusCode).toBe(201);
    });

    it('should retrieve public key bundle', async () => {
      // First upload keys
      await server.inject({
        method: 'POST',
        url: '/keys/upload',
        headers: {
          Authorization: `Bearer ${authToken}`
        },
        payload: {
          identityKey: {
            publicKey: 'test-identity-public-key',
            privateKey: 'test-identity-private-key'
          },
          signedPreKey: {
            id: 1,
            publicKey: 'test-signed-public-key',
            privateKey: 'test-signed-private-key',
            signature: 'test-signature'
          },
          oneTimePreKeys: [
            {
              id: 1,
              publicKey: 'test-onetime-public-1',
              privateKey: 'test-onetime-private-1'
            }
          ]
        }
      });

      // Then retrieve bundle
      const response = await server.inject({
        method: 'GET',
        url: `/keys/bundle/${userId}`,
        headers: {
          Authorization: `Bearer ${authToken}`
        }
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.identityKey).toBeDefined();
      expect(body.signedPreKey).toBeDefined();
      expect(body.oneTimePreKey).toBeDefined();
    });

    it('should rotate signed pre-key', async () => {
      const response = await server.inject({
        method: 'POST',
        url: '/keys/rotate/signed',
        headers: {
          Authorization: `Bearer ${authToken}`
        },
        payload: {
          signedPreKey: {
            id: 2,
            publicKey: 'new-signed-public-key',
            privateKey: 'new-signed-private-key',
            signature: 'new-signature'
          }
        }
      });

      expect(response.statusCode).toBe(200);
    });
  });

  describe('Messaging', () => {
    let user1Token: string;
    let user2Token: string;
    let user1Id: string;
    let user2Id: string;

    beforeEach(async () => {
      // Setup two users
      const user1Register = await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'user1@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'User One'
        }
      });
      user1Id = JSON.parse(user1Register.body).id;

      const user1Login = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'user1@example.com',
          password: 'SecureP@ssw0rd123',
          deviceFingerprint: 'device1'
        }
      });
      user1Token = JSON.parse(user1Login.body).token;

      const user2Register = await server.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'user2@example.com',
          password: 'SecureP@ssw0rd123',
          displayName: 'User Two'
        }
      });
      user2Id = JSON.parse(user2Register.body).id;

      const user2Login = await server.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'user2@example.com',
          password: 'SecureP@ssw0rd123',
          deviceFingerprint: 'device2'
        }
      });
      user2Token = JSON.parse(user2Login.body).token;
    });

    it('should establish a session between users', async () => {
      const response = await server.inject({
        method: 'POST',
        url: `/sessions/${user2Id}`,
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {}
      });

      expect(response.statusCode).toBe(201);
      const body = JSON.parse(response.body);
      expect(body.established).toBe(true);
      expect(body.userId).toBe(user1Id);
      expect(body.peerId).toBe(user2Id);
    });

    it('should send an encrypted message', async () => {
      // First establish session
      await server.inject({
        method: 'POST',
        url: `/sessions/${user2Id}`,
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {}
      });

      // Send message
      const response = await server.inject({
        method: 'POST',
        url: '/messages/send',
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {
          recipientId: user2Id,
          ciphertext: 'encrypted-message-content',
          nonce: 'message-nonce',
          authTag: 'auth-tag',
          dhPublicKey: 'dh-public-key',
          messageNumber: 0,
          previousChainLength: 0
        }
      });

      expect(response.statusCode).toBe(201);
      const body = JSON.parse(response.body);
      expect(body.senderId).toBe(user1Id);
      expect(body.recipientId).toBe(user2Id);
      expect(body.ciphertext).toBeDefined();
    });

    it('should retrieve messages between users', async () => {
      // Send some messages first
      await server.inject({
        method: 'POST',
        url: `/sessions/${user2Id}`,
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {}
      });

      await server.inject({
        method: 'POST',
        url: '/messages/send',
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {
          recipientId: user2Id,
          ciphertext: 'message-1',
          nonce: 'nonce-1',
          authTag: 'tag-1',
          dhPublicKey: 'key-1',
          messageNumber: 0,
          previousChainLength: 0
        }
      });

      // Retrieve messages
      const response = await server.inject({
        method: 'GET',
        url: `/messages/${user1Id}`,
        headers: {
          Authorization: `Bearer ${user2Token}`
        }
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.messages).toBeInstanceOf(Array);
      expect(body.messages.length).toBeGreaterThan(0);
    });

    it('should send message receipt', async () => {
      // Send a message
      await server.inject({
        method: 'POST',
        url: `/sessions/${user2Id}`,
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {}
      });

      const sendResponse = await server.inject({
        method: 'POST',
        url: '/messages/send',
        headers: {
          Authorization: `Bearer ${user1Token}`
        },
        payload: {
          recipientId: user2Id,
          ciphertext: 'message',
          nonce: 'nonce',
          authTag: 'tag',
          dhPublicKey: 'key',
          messageNumber: 0,
          previousChainLength: 0
        }
      });

      const messageId = JSON.parse(sendResponse.body).id;

      // Send receipt
      const response = await server.inject({
        method: 'POST',
        url: `/messages/${messageId}/receipt`,
        headers: {
          Authorization: `Bearer ${user2Token}`
        },
        payload: {
          status: 'delivered'
        }
      });

      expect(response.statusCode).toBe(204);
    });

    it('should generate safety number for verification', async () => {
      const response = await server.inject({
        method: 'GET',
        url: `/verification/${user2Id}/safety-number`,
        headers: {
          Authorization: `Bearer ${user1Token}`
        }
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.safetyNumber).toBeDefined();
      expect(body.qrCode).toBeDefined();
    });
  });

  describe('Health Check', () => {
    it('should return healthy status', async () => {
      const response = await server.inject({
        method: 'GET',
        url: '/health'
      });

      expect(response.statusCode).toBe(200);
      const body = JSON.parse(response.body);
      expect(body.status).toBe('healthy');
      expect(body.timestamp).toBeDefined();
    });
  });
});