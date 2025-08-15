import { v4 as uuidv4 } from 'uuid';
import { Session } from '../entities';
import { KeyManager } from '../crypto/keyManager';
import { DoubleRatchet } from '../crypto/doubleRatchet';
import { SessionRepository } from '../../infra/repositories/sessionRepository';
import { KeyRepository } from '../../infra/repositories/keyRepository';
import { Database } from '../../infra/db';
import sodium from 'libsodium-wrappers';

export interface SessionService {
  establishSession(userId: string, peerId: string): Promise<Session>;
  getSession(userId: string, peerId: string): Promise<Session | null>;
  updateSession(session: Session): Promise<void>;
  deleteSession(sessionId: string): Promise<void>;
  rotateSessionKeys(sessionId: string): Promise<Session>;
}

export class SessionServiceImpl implements SessionService {
  private keyManager: KeyManager;
  private sessionRepository: SessionRepository;
  private keyRepository: KeyRepository;
  
  constructor(
    private db: Database,
    sessionRepository: SessionRepository,
    keyRepository: KeyRepository
  ) {
    this.sessionRepository = sessionRepository;
    this.keyRepository = keyRepository;
  }

  async initialize() {
    this.keyManager = await KeyManager.getInstance();
    await DoubleRatchet.initialize();
  }

  async establishSession(userId: string, peerId: string): Promise<Session> {
    if (!this.keyManager) {
      await this.initialize();
    }

    // Check if session already exists
    const existingSession = await this.sessionRepository.findByUsers(userId, peerId);
    if (existingSession) {
      return existingSession;
    }

    // Get user's identity key (private)
    // In production, this would be retrieved from secure storage
    const userIdentityQuery = 'SELECT * FROM identity_keys WHERE user_id = $1';
    const userIdentityResult = await this.db.query(userIdentityQuery, [userId]);
    if (userIdentityResult.rows.length === 0) {
      throw new Error('User identity key not found');
    }

    // Get peer's public key bundle
    const peerIdentityKey = await this.keyRepository.getIdentityKey(peerId);
    const peerSignedPreKey = await this.keyRepository.getActiveSignedPreKey(peerId);
    const peerOneTimePreKey = await this.keyRepository.getOneTimePreKey(peerId);

    if (!peerIdentityKey || !peerSignedPreKey) {
      throw new Error('Peer keys not available');
    }

    // Generate ephemeral key for X3DH
    const ephemeralKeyPair = this.keyManager.generateX25519KeyPair();

    // Perform X3DH key exchange
    const sharedSecret = this.keyManager.performX3DH(
      '', // User's identity private key (would be from secure storage)
      ephemeralKeyPair.privateKey,
      peerIdentityKey.publicKey,
      peerSignedPreKey.publicKey,
      peerOneTimePreKey?.publicKey
    );

    // Initialize Double Ratchet with shared secret
    const doubleRatchet = new DoubleRatchet(sharedSecret);
    
    // Generate initial DH key pair for Double Ratchet
    const dhKeyPair = doubleRatchet.generateKeyPair();
    await doubleRatchet.initializeAsSender(sodium.from_base64(peerSignedPreKey.publicKey));

    // Create session
    const session: Session = {
      id: uuidv4(),
      userId,
      peerId,
      rootKey: sodium.to_base64(sharedSecret),
      sendingChainKey: sodium.to_base64(new Uint8Array(32)), // Will be derived
      receivingChainKey: sodium.to_base64(new Uint8Array(32)), // Will be derived
      sendingMessageNumber: 0,
      receivingMessageNumber: 0,
      previousSendingChainLength: 0,
      dhSendingKeyPair: {
        publicKey: sodium.to_base64(dhKeyPair.publicKey),
        privateKey: sodium.to_base64(dhKeyPair.privateKey)
      },
      dhReceivingKey: peerSignedPreKey.publicKey,
      createdAt: new Date(),
      updatedAt: new Date()
    };

    // Save session
    await this.sessionRepository.create(session);

    // Consume one-time pre-key if used
    if (peerOneTimePreKey) {
      await this.keyRepository.consumeOneTimePreKey(peerId, peerOneTimePreKey.id);
    }

    return session;
  }

  async getSession(userId: string, peerId: string): Promise<Session | null> {
    return await this.sessionRepository.findByUsers(userId, peerId);
  }

  async updateSession(session: Session): Promise<void> {
    await this.sessionRepository.update(session);
  }

  async deleteSession(sessionId: string): Promise<void> {
    await this.sessionRepository.delete(sessionId);
  }

  async rotateSessionKeys(sessionId: string): Promise<Session> {
    if (!this.keyManager) {
      await this.initialize();
    }

    // Get session from database
    const session = await this.sessionRepository.findById(sessionId);
    if (!session) {
      throw new Error('Session not found');
    }

    // Reconstruct Double Ratchet state
    const doubleRatchet = DoubleRatchet.fromState({
      DHs: session.dhSendingKeyPair ? {
        publicKey: session.dhSendingKeyPair.publicKey,
        privateKey: session.dhSendingKeyPair.privateKey
      } : undefined,
      DHr: session.dhReceivingKey,
      RK: session.rootKey,
      CKs: session.sendingChainKey,
      CKr: session.receivingChainKey,
      Ns: session.sendingMessageNumber,
      Nr: session.receivingMessageNumber,
      PN: session.previousSendingChainLength,
      skippedKeys: []
    });

    // Generate new DH key pair (triggers ratchet)
    const newDHKeyPair = doubleRatchet.generateKeyPair();
    
    // Update session with new state
    const newState = doubleRatchet.exportState();
    
    session.dhSendingKeyPair = {
      publicKey: newState.DHs.publicKey,
      privateKey: newState.DHs.privateKey
    };
    session.rootKey = newState.RK;
    session.sendingChainKey = newState.CKs;
    session.receivingChainKey = newState.CKr;
    session.updatedAt = new Date();

    // Save updated session
    await this.sessionRepository.update(session);

    return session;
  }
}