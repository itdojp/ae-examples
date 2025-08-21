/**
 * Chat Service - Core business logic for encrypted chat
 */

import { v4 as uuidv4 } from 'uuid';
import { 
  User, 
  Message, 
  ChatSession, 
  KeyBundle, 
  SecurityEvent,
  SecurityNumber,
  MessageContent 
} from '../domain/entities.js';
import { CryptoService, IdentityKey, PreKey, OneTimePreKey } from '../crypto/encryption.js';
import { DoubleRatchet, RatchetMessage } from '../crypto/double-ratchet.js';

export interface ChatRepository {
  saveUser(user: User): Promise<void>;
  getUser(userId: string): Promise<User | null>;
  saveMessage(message: Message): Promise<void>;
  getMessages(sessionId: string): Promise<Message[]>;
  saveSession(session: ChatSession): Promise<void>;
  getSession(sessionId: string): Promise<ChatSession | null>;
  saveKeyBundle(bundle: KeyBundle): Promise<void>;
  getKeyBundle(userId: string): Promise<KeyBundle | null>;
}

export class ChatService {
  private sessions: Map<string, DoubleRatchet> = new Map();
  
  constructor(
    private readonly repository: ChatRepository,
    private readonly currentUser: User
  ) {}

  /**
   * Initialize user with encryption keys
   */
  async initializeUser(email: string, displayName: string): Promise<User> {
    const identityKey = await CryptoService.generateIdentityKeyPair();
    const signedPreKey = await CryptoService.generateSignedPreKey(identityKey);
    const oneTimePreKeys = await CryptoService.generateOneTimePreKeys(100);

    const user: User = {
      id: uuidv4(),
      email,
      displayName,
      createdAt: new Date(),
      devices: [],
      trustLevel: 'unverified',
      publicKey: Buffer.from(identityKey.publicKey).toString('base64')
    };

    const keyBundle: KeyBundle = {
      userId: user.id,
      identityKey: Buffer.from(identityKey.publicKey).toString('base64'),
      signedPreKey: {
        id: signedPreKey.id,
        key: Buffer.from(signedPreKey.publicKey).toString('base64'),
        signature: Buffer.from(signedPreKey.signature!).toString('base64')
      },
      oneTimePreKeys: oneTimePreKeys.map(key => ({
        id: key.id,
        key: Buffer.from(key.publicKey).toString('base64')
      }))
    };

    await this.repository.saveUser(user);
    await this.repository.saveKeyBundle(keyBundle);

    return user;
  }

  /**
   * Start a new chat session with another user
   */
  async startSession(recipientId: string): Promise<ChatSession> {
    const recipient = await this.repository.getUser(recipientId);
    if (!recipient) {
      throw new Error('Recipient not found');
    }

    const recipientKeys = await this.repository.getKeyBundle(recipientId);
    if (!recipientKeys) {
      throw new Error('Recipient keys not available');
    }

    // Perform X3DH key agreement
    const sharedSecret = await this.performX3DH(recipientKeys);
    
    // Initialize Double Ratchet
    const ratchet = new DoubleRatchet(
      sharedSecret,
      true,
      Buffer.from(recipientKeys.identityKey, 'base64')
    );

    const sessionId = uuidv4();
    this.sessions.set(sessionId, ratchet);

    const session: ChatSession = {
      id: sessionId,
      participants: [this.currentUser.id, recipientId],
      createdAt: new Date(),
      lastActivity: new Date(),
      verified: false,
      ratchetState: ratchet.getState()
    };

    await this.repository.saveSession(session);
    return session;
  }

  /**
   * Send an encrypted message
   */
  async sendMessage(
    sessionId: string,
    content: MessageContent
  ): Promise<Message> {
    const session = await this.repository.getSession(sessionId);
    if (!session) {
      throw new Error('Session not found');
    }

    let ratchet = this.sessions.get(sessionId);
    if (!ratchet) {
      ratchet = DoubleRatchet.fromState(session.ratchetState);
      this.sessions.set(sessionId, ratchet);
    }

    const encrypted = await ratchet.encrypt(content.getText());
    
    const message: Message = {
      id: uuidv4(),
      senderId: this.currentUser.id,
      recipientId: session.participants.find(p => p !== this.currentUser.id)!,
      ciphertext: Buffer.from(encrypted.ciphertext).toString('base64'),
      nonce: Buffer.from(encrypted.nonce).toString('base64'),
      timestamp: new Date(),
      ephemeralKey: Buffer.from(encrypted.header.dhPublicKey).toString('base64'),
      messageType: 'text',
      status: 'sending'
    };

    await this.repository.saveMessage(message);
    
    // Update session state
    session.ratchetState = ratchet.getState();
    session.lastActivity = new Date();
    await this.repository.saveSession(session);

    return message;
  }

  /**
   * Receive and decrypt a message
   */
  async receiveMessage(
    sessionId: string,
    encryptedMessage: Message
  ): Promise<string> {
    const session = await this.repository.getSession(sessionId);
    if (!session) {
      throw new Error('Session not found');
    }

    let ratchet = this.sessions.get(sessionId);
    if (!ratchet) {
      ratchet = DoubleRatchet.fromState(session.ratchetState);
      this.sessions.set(sessionId, ratchet);
    }

    const ratchetMessage: RatchetMessage = {
      header: {
        dhPublicKey: Buffer.from(encryptedMessage.ephemeralKey!, 'base64'),
        previousChainCount: 0,
        messageNumber: 0
      },
      ciphertext: Buffer.from(encryptedMessage.ciphertext, 'base64'),
      nonce: Buffer.from(encryptedMessage.nonce, 'base64')
    };

    const plaintext = await ratchet.decrypt(ratchetMessage);
    
    // Update session state
    session.ratchetState = ratchet.getState();
    session.lastActivity = new Date();
    await this.repository.saveSession(session);

    // Update message status
    encryptedMessage.status = 'delivered';
    await this.repository.saveMessage(encryptedMessage);

    return plaintext;
  }

  /**
   * Verify session security number
   */
  async verifySession(
    sessionId: string,
    remoteSecurityNumber: string
  ): Promise<boolean> {
    const session = await this.repository.getSession(sessionId);
    if (!session) {
      throw new Error('Session not found');
    }

    const otherUserId = session.participants.find(p => p !== this.currentUser.id)!;
    const otherUser = await this.repository.getUser(otherUserId);
    if (!otherUser) {
      throw new Error('Other user not found');
    }

    const localFingerprint = CryptoService.calculateFingerprint(
      Buffer.from(this.currentUser.publicKey, 'base64'),
      Buffer.from(otherUser.publicKey, 'base64')
    );

    const localSecurityNumber = new SecurityNumber(localFingerprint, remoteSecurityNumber);
    const remoteSecurityNumber2 = new SecurityNumber(remoteSecurityNumber, localFingerprint);
    
    const verified = localSecurityNumber.verify(remoteSecurityNumber2);
    
    if (verified) {
      session.verified = true;
      session.securityNumber = localFingerprint;
      await this.repository.saveSession(session);
      
      // Log security event
      const event: SecurityEvent = {
        id: uuidv4(),
        type: 'verification_completed',
        userId: this.currentUser.id,
        details: { sessionId, otherUserId },
        timestamp: new Date(),
        severity: 'info'
      };
    }

    return verified;
  }

  /**
   * Perform X3DH key agreement
   */
  private async performX3DH(recipientKeys: KeyBundle): Promise<Uint8Array> {
    // Simplified X3DH implementation
    const recipientIdentity = Buffer.from(recipientKeys.identityKey, 'base64');
    const recipientPreKey = Buffer.from(recipientKeys.signedPreKey.key, 'base64');
    
    // Generate ephemeral key
    const ephemeralKey = await CryptoService.generateIdentityKeyPair();
    
    // Perform DH operations
    const dh1 = await CryptoService.performDH(ephemeralKey.privateKey, recipientIdentity);
    const dh2 = await CryptoService.performDH(ephemeralKey.privateKey, recipientPreKey);
    
    // Combine secrets
    const sharedSecret = new Uint8Array(64);
    sharedSecret.set(dh1, 0);
    sharedSecret.set(dh2, 32);
    
    return sharedSecret;
  }

  /**
   * Get all messages for a session
   */
  async getSessionMessages(sessionId: string): Promise<Message[]> {
    return this.repository.getMessages(sessionId);
  }

  /**
   * Delete a message (sender only)
   */
  async deleteMessage(messageId: string): Promise<void> {
    // Implementation for message deletion
    // This would mark the message as deleted in the repository
  }

  /**
   * Rotate encryption keys
   */
  async rotateKeys(): Promise<void> {
    const newIdentityKey = await CryptoService.generateIdentityKeyPair();
    const newSignedPreKey = await CryptoService.generateSignedPreKey(newIdentityKey);
    const newOneTimePreKeys = await CryptoService.generateOneTimePreKeys(100);

    // Update key bundle in repository
    const keyBundle: KeyBundle = {
      userId: this.currentUser.id,
      identityKey: Buffer.from(newIdentityKey.publicKey).toString('base64'),
      signedPreKey: {
        id: newSignedPreKey.id,
        key: Buffer.from(newSignedPreKey.publicKey).toString('base64'),
        signature: Buffer.from(newSignedPreKey.signature!).toString('base64')
      },
      oneTimePreKeys: newOneTimePreKeys.map(key => ({
        id: key.id,
        key: Buffer.from(key.publicKey).toString('base64')
      }))
    };

    await this.repository.saveKeyBundle(keyBundle);

    // Log security event
    const event: SecurityEvent = {
      id: uuidv4(),
      type: 'key_change',
      userId: this.currentUser.id,
      details: { reason: 'scheduled_rotation' },
      timestamp: new Date(),
      severity: 'info'
    };
  }
}