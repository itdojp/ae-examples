import { User, UserId } from '../entities/User';
import { ChatSession, SessionId, DoubleRatchetState } from '../entities/Session';
import { EncryptedMessage, PlainMessage, MessageStatus } from '../entities/Message';
import { CryptoKeyBundle } from '../entities/CryptoKey';
import { E2EEncryptionService } from '../../application/services/EncryptionService';
import { CryptoService } from '../../infrastructure/crypto/CryptoService';
import { DoubleRatchet } from '../../infrastructure/crypto/DoubleRatchet';

export interface DomainEvent {
  aggregateId: string;
  eventType: string;
  eventData: any;
  occurredAt: Date;
}

export class MessageSentEvent implements DomainEvent {
  aggregateId: string;
  eventType = 'MessageSent';
  eventData: EncryptedMessage;
  occurredAt: Date;

  constructor(message: EncryptedMessage) {
    this.aggregateId = message.id;
    this.eventData = message;
    this.occurredAt = new Date();
  }
}

export class SessionVerifiedEvent implements DomainEvent {
  aggregateId: string;
  eventType = 'SessionVerified';
  eventData: { sessionId: SessionId; verifiedAt: Date };
  occurredAt: Date;

  constructor(sessionId: SessionId) {
    this.aggregateId = sessionId;
    this.eventData = { sessionId, verifiedAt: new Date() };
    this.occurredAt = new Date();
  }
}

export class ChatAggregate {
  private domainEvents: DomainEvent[] = [];
  private encryptionService: E2EEncryptionService;
  private cryptoService: CryptoService;
  private doubleRatchet: DoubleRatchet;

  private constructor(
    private readonly session: ChatSession,
    private readonly messages: EncryptedMessage[],
    private readonly participants: User[]
  ) {
    this.encryptionService = new E2EEncryptionService();
    this.cryptoService = CryptoService.getInstance();
    this.doubleRatchet = new DoubleRatchet();
  }

  static async create(
    initiator: User,
    recipient: User,
    initiatorKeyBundle: CryptoKeyBundle,
    recipientPublicKey: Uint8Array
  ): Promise<ChatAggregate> {
    const cryptoService = CryptoService.getInstance();
    await cryptoService.init();
    
    const doubleRatchet = new DoubleRatchet();
    await doubleRatchet.init();
    
    const sharedSecret = await cryptoService.deriveSharedSecret(
      recipientPublicKey,
      initiatorKeyBundle.identityKey.privateKey
    );
    
    const ratchetState = await doubleRatchet.initializeSession(
      sharedSecret,
      recipientPublicKey
    );
    
    const session: ChatSession = {
      id: ChatAggregate.generateSessionId(),
      participants: [initiator.id, recipient.id],
      ratchetState,
      messageKeys: [],
      verified: false,
      createdAt: new Date(),
      lastActivityAt: new Date()
    };
    
    return new ChatAggregate(session, [], [initiator, recipient]);
  }

  async sendMessage(
    content: string,
    sender: User
  ): Promise<EncryptedMessage> {
    await this.encryptionService.init();
    
    const recipient = this.getRecipient(sender);
    if (!recipient) {
      throw new Error('Recipient not found in chat');
    }
    
    const encrypted = await this.encryptionService.encryptMessage(
      content,
      new Uint8Array(32),
      this.session.ratchetState
    );
    
    encrypted.senderId = sender.id;
    encrypted.recipientId = recipient.id;
    
    this.messages.push(encrypted);
    this.session.lastActivityAt = new Date();
    
    this.addDomainEvent(new MessageSentEvent(encrypted));
    
    return encrypted;
  }

  async receiveMessage(
    encrypted: EncryptedMessage
  ): Promise<PlainMessage> {
    await this.encryptionService.init();
    
    const plaintext = await this.encryptionService.decryptMessage(
      encrypted,
      new Uint8Array(32),
      this.session.ratchetState
    );
    
    const plainMessage: PlainMessage = {
      id: encrypted.id,
      senderId: encrypted.senderId,
      recipientId: encrypted.recipientId,
      content: plaintext,
      timestamp: encrypted.timestamp,
      status: MessageStatus.DELIVERED
    };
    
    this.messages.push(encrypted);
    this.session.lastActivityAt = new Date();
    
    return plainMessage;
  }

  verifySession(): void {
    if (this.session.verified) {
      throw new Error('Session already verified');
    }
    
    this.session.verified = true;
    this.addDomainEvent(new SessionVerifiedEvent(this.session.id));
  }

  isVerified(): boolean {
    return this.session.verified;
  }

  getMessages(): EncryptedMessage[] {
    return [...this.messages];
  }

  getSession(): ChatSession {
    return { ...this.session };
  }

  getParticipants(): User[] {
    return [...this.participants];
  }

  getOtherParticipant(currentUser: User): User | undefined {
    return this.participants.find(p => p.id !== currentUser.id);
  }

  private getRecipient(sender: User): User | undefined {
    return this.participants.find(p => p.id !== sender.id);
  }

  private addDomainEvent(event: DomainEvent): void {
    this.domainEvents.push(event);
  }

  getUncommittedEvents(): DomainEvent[] {
    return [...this.domainEvents];
  }

  markEventsAsCommitted(): void {
    this.domainEvents = [];
  }

  private static generateSessionId(): SessionId {
    return `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }
}