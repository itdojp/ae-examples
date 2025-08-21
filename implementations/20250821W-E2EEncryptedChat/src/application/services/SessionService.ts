import { UserId } from '../../domain/entities/User';
import { ChatSession, MessageKey } from '../../domain/entities/Session';
import { SecurityNumber } from '../../domain/value-objects/SecurityNumber';
import { ChatRepository } from '../../domain/repositories/ChatRepository';
import { UserRepository } from '../../domain/repositories/UserRepository';
import { KeyRepository } from '../../domain/repositories/KeyRepository';
import { ChatAggregate } from '../../domain/aggregates/ChatAggregate';
import { CryptoService } from '../../infrastructure/crypto/CryptoService';

export interface SessionService {
  establishSession(
    initiator: UserId,
    recipient: UserId
  ): Promise<ChatSession>;
  
  ratchetForward(
    session: ChatSession
  ): Promise<MessageKey>;
  
  verifySession(
    session: ChatSession,
    securityNumber: SecurityNumber
  ): Promise<boolean>;
}

export class SessionServiceImpl implements SessionService {
  private cryptoService: CryptoService;

  constructor(
    private chatRepository: ChatRepository,
    private userRepository: UserRepository,
    private keyRepository: KeyRepository
  ) {
    this.cryptoService = CryptoService.getInstance();
  }

  async establishSession(
    initiatorId: UserId,
    recipientId: UserId
  ): Promise<ChatSession> {
    const initiator = await this.userRepository.findById(initiatorId);
    const recipient = await this.userRepository.findById(recipientId);

    if (!initiator || !recipient) {
      throw new Error('User not found');
    }

    const initiatorKeyBundle = await this.keyRepository.getKeyBundle(initiatorId);
    const recipientKeyBundle = await this.keyRepository.getKeyBundle(recipientId);

    if (!initiatorKeyBundle || !recipientKeyBundle) {
      throw new Error('Key bundle not found');
    }

    const chat = await ChatAggregate.create(
      initiator,
      recipient,
      initiatorKeyBundle,
      recipientKeyBundle.identityKey.publicKey
    );

    await this.chatRepository.save(chat);
    
    return chat.getSession();
  }

  async ratchetForward(session: ChatSession): Promise<MessageKey> {
    await this.cryptoService.init();
    
    const messageKey = await this.cryptoService.generateHMAC(
      session.ratchetState.sendingChainKey,
      new TextEncoder().encode('message')
    );
    
    return messageKey;
  }

  async verifySession(
    session: ChatSession,
    securityNumber: SecurityNumber
  ): Promise<boolean> {
    const chats = await this.chatRepository.findByParticipants(session.participants);
    
    if (chats.length === 0) {
      return false;
    }

    const chat = chats[0];
    
    try {
      chat.verifySession();
      await this.chatRepository.save(chat);
      return true;
    } catch (error) {
      return false;
    }
  }

  async getOrCreateSession(
    userId1: UserId,
    userId2: UserId
  ): Promise<ChatSession> {
    const existingChats = await this.chatRepository.findByParticipants([userId1, userId2]);
    
    if (existingChats.length > 0) {
      return existingChats[0].getSession();
    }
    
    return await this.establishSession(userId1, userId2);
  }

  async generateSecurityNumber(
    session: ChatSession
  ): Promise<SecurityNumber> {
    await this.cryptoService.init();
    
    const localFingerprint = await this.generateFingerprint(
      session.ratchetState.localPublicKey
    );
    const remoteFingerprint = await this.generateFingerprint(
      session.ratchetState.remotePublicKey
    );
    
    return new SecurityNumber(localFingerprint, remoteFingerprint);
  }

  private async generateFingerprint(publicKey: Uint8Array): Promise<string> {
    const hash = await this.cryptoService.hash(publicKey);
    const hex = Array.from(hash.slice(0, 16))
      .map(b => b.toString(16).padStart(2, '0'))
      .join('');
    return hex.toUpperCase();
  }
}