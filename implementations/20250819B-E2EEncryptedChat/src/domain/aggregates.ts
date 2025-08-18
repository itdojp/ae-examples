/**
 * Domain Aggregates and Repositories for E2E Encrypted Chat Application - Phase 5
 * 
 * This file contains aggregate roots and repository interfaces following DDD principles.
 * Aggregates ensure consistency boundaries and encapsulate business invariants.
 */

import {
  User,
  Device,
  EncryptedMessage,
  ChatSession,
  SecurityVerification,
  VerificationStatus,
  CryptoKeyBundle
} from './entities';
import {
  UserId,
  DeviceId,
  SessionId,
  MessageId,
  Email,
  Timestamp,
  CipherText,
  Nonce,
  AuthenticationTag,
  SecurityNumber
} from './value-objects';
import {
  DomainEvent,
  MessageEncryptedEvent,
  KeyRotatedEvent,
  SessionEstablishedEvent,
  IEncryptionService,
  IKeyManagementService,
  ISessionService,
  IVerificationService,
  PublicKeyBundle
} from './services';

/**
 * Additional domain events specific to aggregates
 */
export interface MessageSentEvent extends DomainEvent {
  readonly messageId: MessageId;
  readonly senderId: UserId;
  readonly recipientId: UserId;
  readonly sessionId: SessionId;
  readonly messageNumber: number;
}

export interface MessageDeliveredEvent extends DomainEvent {
  readonly messageId: MessageId;
  readonly recipientId: UserId;
  readonly deliveredAt: Timestamp;
}

export interface MessageReadEvent extends DomainEvent {
  readonly messageId: MessageId;
  readonly recipientId: UserId;
  readonly readAt: Timestamp;
}

export interface SessionVerifiedEvent extends DomainEvent {
  readonly sessionId: SessionId;
  readonly verificationId: string;
  readonly verifiedBy: UserId;
}

export interface UserRegisteredEvent extends DomainEvent {
  readonly userId: UserId;
  readonly email: Email;
  readonly registeredAt: Timestamp;
}

export interface DeviceAddedEvent extends DomainEvent {
  readonly userId: UserId;
  readonly deviceId: DeviceId;
  readonly deviceName: string;
  readonly addedAt: Timestamp;
}

export interface DeviceRevokedEvent extends DomainEvent {
  readonly userId: UserId;
  readonly deviceId: DeviceId;
  readonly revokedAt: Timestamp;
}

/**
 * Base aggregate root with event sourcing capabilities
 */
abstract class AggregateRoot {
  private readonly _events: DomainEvent[] = [];
  protected _version: number = 0;

  protected addEvent(event: DomainEvent): void {
    this._events.push(event);
  }

  getUncommittedEvents(): ReadonlyArray<DomainEvent> {
    return [...this._events];
  }

  markEventsAsCommitted(): void {
    this._events.length = 0;
    this._version++;
  }

  get version(): number {
    return this._version;
  }

  protected generateEventId(): string {
    return MessageId.generate().value;
  }
}

/**
 * Chat Aggregate - Main aggregate root for chat sessions
 * 
 * Manages the lifecycle of chat sessions, message encryption/decryption,
 * and ensures consistency of the chat state.
 */
export class ChatAggregate extends AggregateRoot {
  private readonly _sessions: Map<string, ChatSession> = new Map();
  private readonly _messages: Map<string, EncryptedMessage> = new Map();
  private readonly _verifications: Map<string, SecurityVerification> = new Map();

  private constructor(
    private readonly _id: SessionId,
    private readonly _encryptionService: IEncryptionService,
    private readonly _sessionService: ISessionService,
    private readonly _verificationService: IVerificationService
  ) {
    super();
  }

  static create(
    id: SessionId,
    encryptionService: IEncryptionService,
    sessionService: ISessionService,
    verificationService: IVerificationService
  ): ChatAggregate {
    return new ChatAggregate(id, encryptionService, sessionService, verificationService);
  }

  get id(): SessionId {
    return this._id;
  }

  get sessions(): ReadonlyArray<ChatSession> {
    return Array.from(this._sessions.values());
  }

  get messages(): ReadonlyArray<EncryptedMessage> {
    return Array.from(this._messages.values());
  }

  /**
   * Establishes a new chat session between two users
   */
  async establishSession(
    participantAId: UserId,
    participantADeviceId: DeviceId,
    participantBId: UserId,
    participantBDeviceId: DeviceId,
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle
  ): Promise<ChatSession> {
    // Validate participants are different
    if (participantAId.equals(participantBId) && participantADeviceId.equals(participantBDeviceId)) {
      throw new Error('Cannot establish session between same user and device');
    }

    // Check if session already exists
    const existingSession = this.findSessionBetween(
      participantAId,
      participantADeviceId,
      participantBId,
      participantBDeviceId
    );
    
    if (existingSession && existingSession.isActive) {
      throw new Error('Active session already exists between these participants');
    }

    // Create new session
    const session = await this._sessionService.createSession(
      participantAId,
      participantADeviceId,
      participantBId,
      participantBDeviceId,
      localKeyBundle,
      remotePublicKeyBundle
    );

    this._sessions.set(session.id.value, session);

    // Add domain event
    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._id.value,
      sessionId: session.id,
      participantAId,
      participantBId
    } as SessionEstablishedEvent);

    return session;
  }

  /**
   * Sends an encrypted message within a session
   */
  async sendMessage(
    sessionId: SessionId,
    plaintext: string,
    senderId: UserId,
    senderDeviceId: DeviceId,
    recipientId: UserId,
    recipientDeviceId: DeviceId
  ): Promise<EncryptedMessage> {
    const session = this._sessions.get(sessionId.value);
    if (!session) {
      throw new Error('Session not found');
    }

    if (!session.isActive) {
      throw new Error('Cannot send message to inactive session');
    }

    if (!session.isParticipant(senderId, senderDeviceId)) {
      throw new Error('Sender is not a participant in this session');
    }

    if (!session.isParticipant(recipientId, recipientDeviceId)) {
      throw new Error('Recipient is not a participant in this session');
    }

    // Encrypt the message
    const encryptionResult = await this._encryptionService.encryptMessage(
      plaintext,
      session,
      senderDeviceId
    );

    // Create encrypted message
    const messageId = MessageId.generate();
    const message = EncryptedMessage.create(
      messageId,
      senderId,
      senderDeviceId,
      recipientId,
      recipientDeviceId,
      sessionId,
      encryptionResult.cipherText,
      encryptionResult.nonce,
      encryptionResult.authTag,
      session.ratchetState.sendingMessageNumber
    );

    // Update session with new message and ratchet state
    session.addMessage(message);
    session.updateRatchetState(encryptionResult.updatedRatchetState);

    // Store message
    this._messages.set(messageId.value, message);

    // Add domain events
    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._id.value,
      messageId,
      senderId,
      recipientId,
      sessionId,
      messageNumber: message.messageNumber
    } as MessageSentEvent);

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._id.value,
      messageId,
      senderId,
      recipientId,
      sessionId
    } as MessageEncryptedEvent);

    return message;
  }

  /**
   * Decrypts and processes a received message
   */
  async receiveMessage(message: EncryptedMessage): Promise<string> {
    const session = this._sessions.get(message.sessionId.value);
    if (!session) {
      throw new Error('Session not found for message');
    }

    if (!session.isActive) {
      throw new Error('Cannot receive message for inactive session');
    }

    // Decrypt the message
    const decryptionResult = await this._encryptionService.decryptMessage(
      message,
      session,
      message.recipientDeviceId
    );

    // Update session ratchet state
    session.updateRatchetState(decryptionResult.updatedRatchetState);

    // Store message if not already present
    if (!this._messages.has(message.id.value)) {
      session.addMessage(message);
      this._messages.set(message.id.value, message);
    }

    return decryptionResult.plaintext;
  }

  /**
   * Marks a message as delivered
   */
  markMessageDelivered(messageId: MessageId): void {
    const message = this._messages.get(messageId.value);
    if (!message) {
      throw new Error('Message not found');
    }

    message.markAsDelivered();

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._id.value,
      messageId,
      recipientId: message.recipientId,
      deliveredAt: message.deliveredAt!
    } as MessageDeliveredEvent);
  }

  /**
   * Marks a message as read
   */
  markMessageRead(messageId: MessageId): void {
    const message = this._messages.get(messageId.value);
    if (!message) {
      throw new Error('Message not found');
    }

    message.markAsRead();

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._id.value,
      messageId,
      recipientId: message.recipientId,
      readAt: message.readAt!
    } as MessageReadEvent);
  }

  /**
   * Initiates security verification between users
   */
  async initiateVerification(userAId: UserId, userBId: UserId): Promise<SecurityVerification> {
    const verification = await this._verificationService.initiateVerification(userAId, userBId);
    const verificationKey = `${userAId.value}-${userBId.value}`;
    this._verifications.set(verificationKey, verification);
    return verification;
  }

  /**
   * Verifies security number for a verification
   */
  async verifySecurityNumber(
    userAId: UserId,
    userBId: UserId,
    securityNumber: SecurityNumber,
    verifyingUserId: UserId
  ): Promise<boolean> {
    const verificationKey = `${userAId.value}-${userBId.value}`;
    const verification = this._verifications.get(verificationKey);
    
    if (!verification) {
      throw new Error('Verification not found');
    }

    const isValid = await this._verificationService.verifySecurityNumber(
      verification,
      securityNumber,
      verifyingUserId
    );

    if (isValid && verification.isFullyVerified()) {
      this.addEvent({
        eventId: this.generateEventId(),
        timestamp: Timestamp.now(),
        aggregateId: this._id.value,
        sessionId: this._id, // Using aggregate id as session id for this event
        verificationId: verificationKey,
        verifiedBy: verifyingUserId
      } as SessionVerifiedEvent);
    }

    return isValid;
  }

  /**
   * Terminates a chat session
   */
  terminateSession(sessionId: SessionId): void {
    const session = this._sessions.get(sessionId.value);
    if (!session) {
      throw new Error('Session not found');
    }

    session.deactivate();
  }

  /**
   * Gets active sessions for a user and device
   */
  getActiveSessionsForUser(userId: UserId, deviceId: DeviceId): ReadonlyArray<ChatSession> {
    return this.sessions.filter(session => 
      session.isActive && session.isParticipant(userId, deviceId)
    );
  }

  /**
   * Gets undelivered messages for a user and device
   */
  getUndeliveredMessagesForUser(userId: UserId, deviceId: DeviceId): ReadonlyArray<EncryptedMessage> {
    return this.messages.filter(message =>
      message.isReceivedBy(userId, deviceId) && !message.isDelivered
    );
  }

  private findSessionBetween(
    userAId: UserId,
    deviceAId: DeviceId,
    userBId: UserId,
    deviceBId: DeviceId
  ): ChatSession | undefined {
    return this.sessions.find(session =>
      (session.isParticipant(userAId, deviceAId) && session.isParticipant(userBId, deviceBId))
    );
  }
}

/**
 * User Aggregate - Manages user identity and devices
 * 
 * Handles user registration, device management, and key lifecycle.
 */
export class UserAggregate extends AggregateRoot {
  private constructor(
    private readonly _user: User,
    private readonly _keyManagementService: IKeyManagementService
  ) {
    super();
  }

  static create(user: User, keyManagementService: IKeyManagementService): UserAggregate {
    const aggregate = new UserAggregate(user, keyManagementService);
    
    aggregate.addEvent({
      eventId: aggregate.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: user.id.value,
      userId: user.id,
      email: user.email,
      registeredAt: user.createdAt
    } as UserRegisteredEvent);

    return aggregate;
  }

  static fromExisting(user: User, keyManagementService: IKeyManagementService): UserAggregate {
    return new UserAggregate(user, keyManagementService);
  }

  get user(): User {
    return this._user;
  }

  get id(): UserId {
    return this._user.id;
  }

  /**
   * Adds a new device to the user
   */
  addDevice(device: Device): void {
    if (this._user.hasMaxDevices()) {
      throw new Error('Maximum number of devices reached');
    }

    this._user.addDevice(device);

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._user.id.value,
      userId: this._user.id,
      deviceId: device.id,
      deviceName: device.name,
      addedAt: device.registrationTimestamp
    } as DeviceAddedEvent);
  }

  /**
   * Removes a device from the user
   */
  async removeDevice(deviceId: DeviceId): Promise<void> {
    const device = this._user.getDevice(deviceId);
    if (!device) {
      throw new Error('Device not found');
    }

    // Revoke device keys
    await this._keyManagementService.revokeDevice(this._user.id, deviceId);

    // Remove device from user
    this._user.removeDevice(deviceId);

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._user.id.value,
      userId: this._user.id,
      deviceId,
      revokedAt: Timestamp.now()
    } as DeviceRevokedEvent);
  }

  /**
   * Rotates keys for a specific device
   */
  async rotateDeviceKeys(deviceId: DeviceId): Promise<void> {
    const device = this._user.getDevice(deviceId);
    if (!device) {
      throw new Error('Device not found');
    }

    if (!device.isActive) {
      throw new Error('Cannot rotate keys for inactive device');
    }

    await this._keyManagementService.rotateKeys(this._user.id, deviceId);

    this.addEvent({
      eventId: this.generateEventId(),
      timestamp: Timestamp.now(),
      aggregateId: this._user.id.value,
      userId: this._user.id,
      deviceId,
      keyType: 'identity'
    } as KeyRotatedEvent);
  }

  /**
   * Verifies the user account
   */
  verifyUser(): void {
    this._user.verify();
  }

  /**
   * Updates device last seen timestamp
   */
  updateDeviceActivity(deviceId: DeviceId): void {
    const device = this._user.getDevice(deviceId);
    if (!device) {
      throw new Error('Device not found');
    }

    device.updateLastSeen();
  }

  /**
   * Gets active devices for the user
   */
  getActiveDevices(): ReadonlyArray<Device> {
    return this._user.getActiveDevices();
  }

  /**
   * Checks if user can add more devices
   */
  canAddDevice(): boolean {
    return !this._user.hasMaxDevices();
  }
}

/**
 * Repository interface for chat aggregates
 */
export interface IChatRepository {
  save(aggregate: ChatAggregate): Promise<void>;
  findById(id: SessionId): Promise<ChatAggregate | null>;
  findByParticipant(userId: UserId, deviceId: DeviceId): Promise<ChatAggregate[]>;
  delete(id: SessionId): Promise<void>;
}

/**
 * Repository interface for user aggregates
 */
export interface IUserRepository {
  save(aggregate: UserAggregate): Promise<void>;
  findById(id: UserId): Promise<UserAggregate | null>;
  findByEmail(email: Email): Promise<UserAggregate | null>;
  findByDeviceId(deviceId: DeviceId): Promise<UserAggregate | null>;
  delete(id: UserId): Promise<void>;
  exists(id: UserId): Promise<boolean>;
}

/**
 * Repository interface for cryptographic keys
 */
export interface IKeyRepository {
  saveKeyBundle(deviceId: DeviceId, keyBundle: CryptoKeyBundle): Promise<void>;
  findKeyBundle(deviceId: DeviceId): Promise<CryptoKeyBundle | null>;
  savePublicKeyBundle(deviceId: DeviceId, publicKeyBundle: PublicKeyBundle): Promise<void>;
  findPublicKeyBundle(deviceId: DeviceId): Promise<PublicKeyBundle | null>;
  revokeKeys(deviceId: DeviceId): Promise<void>;
  deleteKeys(deviceId: DeviceId): Promise<void>;
}

/**
 * Repository interface for messages
 */
export interface IMessageRepository {
  save(message: EncryptedMessage): Promise<void>;
  findById(id: MessageId): Promise<EncryptedMessage | null>;
  findBySession(sessionId: SessionId): Promise<EncryptedMessage[]>;
  findUndeliveredByRecipient(userId: UserId, deviceId: DeviceId): Promise<EncryptedMessage[]>;
  markAsDelivered(messageId: MessageId): Promise<void>;
  markAsRead(messageId: MessageId): Promise<void>;
  delete(id: MessageId): Promise<void>;
}

/**
 * Repository interface for security verifications
 */
export interface IVerificationRepository {
  save(verification: SecurityVerification): Promise<void>;
  findByUsers(userAId: UserId, userBId: UserId): Promise<SecurityVerification | null>;
  findByUser(userId: UserId): Promise<SecurityVerification[]>;
  delete(userAId: UserId, userBId: UserId): Promise<void>;
}