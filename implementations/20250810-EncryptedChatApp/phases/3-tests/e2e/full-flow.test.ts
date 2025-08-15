import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { FastifyInstance } from 'fastify';
import { WebSocket } from 'ws';
import { Database } from '../../src/infra/db';
import { KeyManager } from '../../src/domain/crypto/keyManager';
import app from '../../src/api/server';

describe('E2E Full Flow Test', () => {
  let server: FastifyInstance;
  let db: Database;
  let keyManager: KeyManager;
  let alice: any = {};
  let bob: any = {};
  let wsAlice: WebSocket;
  let wsBob: WebSocket;

  beforeAll(async () => {
    // Initialize services
    db = new Database(process.env.DATABASE_URL || 'postgresql://app:app@localhost:5432/e2echat_test');
    keyManager = await KeyManager.getInstance();
    
    // Start server
    server = app;
    await server.listen({ port: 3001, host: '127.0.0.1' });
    
    // Clean database
    await db.query('TRUNCATE TABLE users, devices, identity_keys, signed_pre_keys, one_time_pre_keys, sessions, messages CASCADE');
  });

  afterAll(async () => {
    if (wsAlice) wsAlice.close();
    if (wsBob) wsBob.close();
    await server.close();
    await db.close();
  });

  it('should complete full E2E encrypted chat flow', async () => {
    // Step 1: Register Alice
    const aliceRegister = await server.inject({
      method: 'POST',
      url: '/auth/register',
      payload: {
        email: 'alice@example.com',
        password: 'AliceP@ssw0rd123',
        displayName: 'Alice'
      }
    });
    expect(aliceRegister.statusCode).toBe(201);
    alice.user = JSON.parse(aliceRegister.body);

    // Step 2: Register Bob
    const bobRegister = await server.inject({
      method: 'POST',
      url: '/auth/register',
      payload: {
        email: 'bob@example.com',
        password: 'BobP@ssw0rd123',
        displayName: 'Bob'
      }
    });
    expect(bobRegister.statusCode).toBe(201);
    bob.user = JSON.parse(bobRegister.body);

    // Step 3: Login Alice
    const aliceLogin = await server.inject({
      method: 'POST',
      url: '/auth/login',
      payload: {
        email: 'alice@example.com',
        password: 'AliceP@ssw0rd123',
        deviceFingerprint: 'alice-device-001'
      }
    });
    expect(aliceLogin.statusCode).toBe(200);
    alice.auth = JSON.parse(aliceLogin.body);

    // Step 4: Login Bob
    const bobLogin = await server.inject({
      method: 'POST',
      url: '/auth/login',
      payload: {
        email: 'bob@example.com',
        password: 'BobP@ssw0rd123',
        deviceFingerprint: 'bob-device-001'
      }
    });
    expect(bobLogin.statusCode).toBe(200);
    bob.auth = JSON.parse(bobLogin.body);

    // Step 5: Generate and upload Alice's keys
    alice.identityKey = keyManager.generateIdentityKeyPair(alice.user.id);
    alice.signedPreKey = keyManager.generateSignedPreKey(
      alice.user.id,
      alice.identityKey.privateKey!,
      1
    );
    alice.oneTimePreKeys = keyManager.generateOneTimePreKeys(alice.user.id, 1, 10);

    const aliceKeysUpload = await server.inject({
      method: 'POST',
      url: '/keys/upload',
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      },
      payload: {
        identityKey: {
          publicKey: alice.identityKey.publicKey,
          privateKey: alice.identityKey.privateKey
        },
        signedPreKey: {
          id: alice.signedPreKey.id,
          publicKey: alice.signedPreKey.publicKey,
          privateKey: alice.signedPreKey.privateKey,
          signature: alice.signedPreKey.signature
        },
        oneTimePreKeys: alice.oneTimePreKeys.map(k => ({
          id: k.id,
          publicKey: k.publicKey,
          privateKey: k.privateKey
        }))
      }
    });
    expect(aliceKeysUpload.statusCode).toBe(201);

    // Step 6: Generate and upload Bob's keys
    bob.identityKey = keyManager.generateIdentityKeyPair(bob.user.id);
    bob.signedPreKey = keyManager.generateSignedPreKey(
      bob.user.id,
      bob.identityKey.privateKey!,
      1
    );
    bob.oneTimePreKeys = keyManager.generateOneTimePreKeys(bob.user.id, 1, 10);

    const bobKeysUpload = await server.inject({
      method: 'POST',
      url: '/keys/upload',
      headers: {
        Authorization: `Bearer ${bob.auth.token}`
      },
      payload: {
        identityKey: {
          publicKey: bob.identityKey.publicKey,
          privateKey: bob.identityKey.privateKey
        },
        signedPreKey: {
          id: bob.signedPreKey.id,
          publicKey: bob.signedPreKey.publicKey,
          privateKey: bob.signedPreKey.privateKey,
          signature: bob.signedPreKey.signature
        },
        oneTimePreKeys: bob.oneTimePreKeys.map(k => ({
          id: k.id,
          publicKey: k.publicKey,
          privateKey: k.privateKey
        }))
      }
    });
    expect(bobKeysUpload.statusCode).toBe(201);

    // Step 7: Alice fetches Bob's key bundle
    const bobKeyBundle = await server.inject({
      method: 'GET',
      url: `/keys/bundle/${bob.user.id}`,
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      }
    });
    expect(bobKeyBundle.statusCode).toBe(200);
    bob.keyBundle = JSON.parse(bobKeyBundle.body);

    // Step 8: Alice establishes session with Bob
    const sessionEstablish = await server.inject({
      method: 'POST',
      url: `/sessions/${bob.user.id}`,
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      },
      payload: {}
    });
    expect(sessionEstablish.statusCode).toBe(201);
    alice.session = JSON.parse(sessionEstablish.body);

    // Step 9: Connect WebSockets
    await new Promise<void>((resolve) => {
      wsAlice = new WebSocket('ws://127.0.0.1:3001/ws');
      wsAlice.on('open', () => {
        wsAlice.send(JSON.stringify({
          type: 'auth',
          token: alice.auth.token
        }));
      });
      wsAlice.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.type === 'auth' && msg.payload.success) {
          resolve();
        }
      });
    });

    await new Promise<void>((resolve) => {
      wsBob = new WebSocket('ws://127.0.0.1:3001/ws');
      wsBob.on('open', () => {
        wsBob.send(JSON.stringify({
          type: 'auth',
          token: bob.auth.token
        }));
      });
      wsBob.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.type === 'auth' && msg.payload.success) {
          resolve();
        }
      });
    });

    // Step 10: Alice sends encrypted message to Bob
    const plaintext = 'Hello Bob! This is a secret message.';
    const encrypted = keyManager.encryptMessage(
      plaintext,
      new Uint8Array(32).fill(42) // Mock shared secret
    );

    const sendMessage = await server.inject({
      method: 'POST',
      url: '/messages/send',
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      },
      payload: {
        recipientId: bob.user.id,
        ciphertext: encrypted.ciphertext,
        nonce: encrypted.nonce,
        authTag: encrypted.authTag,
        dhPublicKey: 'alice-dh-public',
        messageNumber: 0,
        previousChainLength: 0
      }
    });
    expect(sendMessage.statusCode).toBe(201);
    const sentMessage = JSON.parse(sendMessage.body);

    // Step 11: Bob receives message via WebSocket
    const messageReceived = await new Promise<any>((resolve) => {
      wsBob.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        if (msg.type === 'message') {
          resolve(msg.payload);
        }
      });
      
      // Simulate message delivery via WebSocket
      wsAlice.send(JSON.stringify({
        type: 'message',
        payload: {
          recipientId: bob.user.id,
          messageId: sentMessage.id,
          ciphertext: encrypted.ciphertext,
          nonce: encrypted.nonce,
          authTag: encrypted.authTag
        }
      }));
    });

    // Step 12: Bob fetches messages
    const getMessages = await server.inject({
      method: 'GET',
      url: `/messages/${alice.user.id}`,
      headers: {
        Authorization: `Bearer ${bob.auth.token}`
      }
    });
    expect(getMessages.statusCode).toBe(200);
    const messages = JSON.parse(getMessages.body);
    expect(messages.messages).toHaveLength(1);
    expect(messages.messages[0].senderId).toBe(alice.user.id);

    // Step 13: Bob sends delivery receipt
    const sendReceipt = await server.inject({
      method: 'POST',
      url: `/messages/${sentMessage.id}/receipt`,
      headers: {
        Authorization: `Bearer ${bob.auth.token}`
      },
      payload: {
        status: 'delivered'
      }
    });
    expect(sendReceipt.statusCode).toBe(204);

    // Step 14: Verify safety number
    const safetyNumber = await server.inject({
      method: 'GET',
      url: `/verification/${bob.user.id}/safety-number`,
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      }
    });
    expect(safetyNumber.statusCode).toBe(200);
    const safety = JSON.parse(safetyNumber.body);
    expect(safety.safetyNumber).toBeDefined();
    expect(safety.qrCode).toBeDefined();

    // Step 15: Mark Bob as verified
    const verifyUser = await server.inject({
      method: 'POST',
      url: `/verification/${bob.user.id}/verify`,
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      }
    });
    expect(verifyUser.statusCode).toBe(204);

    // Step 16: Enable 2FA for Alice
    const enable2FA = await server.inject({
      method: 'POST',
      url: '/auth/2fa/enable',
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      }
    });
    expect(enable2FA.statusCode).toBe(200);
    const twoFA = JSON.parse(enable2FA.body);
    expect(twoFA.secret).toBeDefined();
    expect(twoFA.backupCodes).toHaveLength(10);

    // Step 17: Rotate Alice's signed pre-key
    const newSignedPreKey = keyManager.generateSignedPreKey(
      alice.user.id,
      alice.identityKey.privateKey!,
      2
    );
    
    const rotateKey = await server.inject({
      method: 'POST',
      url: '/keys/rotate/signed',
      headers: {
        Authorization: `Bearer ${alice.auth.token}`
      },
      payload: {
        signedPreKey: {
          id: newSignedPreKey.id,
          publicKey: newSignedPreKey.publicKey,
          privateKey: newSignedPreKey.privateKey,
          signature: newSignedPreKey.signature
        }
      }
    });
    expect(rotateKey.statusCode).toBe(200);

    // Step 18: Request more one-time pre-keys
    const requestKeys = await server.inject({
      method: 'POST',
      url: `/keys/one-time/${alice.user.id}`,
      headers: {
        Authorization: `Bearer ${bob.auth.token}`
      },
      payload: {
        count: 5
      }
    });
    expect(requestKeys.statusCode).toBe(200);
    const oneTimeKeys = JSON.parse(requestKeys.body);
    expect(oneTimeKeys.keys).toHaveLength(5);

    console.log('✅ Full E2E encrypted chat flow completed successfully!');
  });
});