/**
 * Domain Entities for E2E Encrypted Chat Application - Phase 5
 * 
 * This file contains the core domain entities following DDD principles.
 * Each entity has a unique identity and encapsulates business logic.
 */

import { 
  UserId, 
  Email, 
  DeviceId, 
  SessionId, 
  MessageId, 
  Timestamp,
  CipherText,
  Nonce,
  AuthenticationTag,
  SecurityNumber
} from './value-objects';

/**
 * Represents the different types of cryptographic keys used in the E2E encryption
 */
export interface CryptoKeyBundle {
  readonly identityKey: CryptoKey; // Long-term identity key
  readonly ephemeralKey: CryptoKey; // Short-term ephemeral key
  readonly preKeys: ReadonlyArray<CryptoKey>; // One-time pre-keys
  readonly signedPreKey: {
    readonly key: CryptoKey;
    readonly signature: ArrayBuffer;
    readonly timestamp: Timestamp;
  };
  readonly symmetricKey?: CryptoKey; // For message encryption
}

/**
 * Represents a device that can participate in encrypted communications
 */
export class Device {
  private constructor(
    private readonly _id: DeviceId,
    private readonly _userId: UserId,
    private readonly _name: string,
    private readonly _keyBundle: CryptoKeyBundle,
    private readonly _registrationTimestamp: Timestamp,
    private _isActive: boolean = true,
    private _lastSeenTimestamp?: Timestamp
  ) {}

  static create(
    id: DeviceId,
    userId: UserId,
    name: string,
    keyBundle: CryptoKeyBundle
  ): Device {
    if (name.trim().length === 0) {
      throw new Error('Device name cannot be empty');
    }
    
    return new Device(
      id,
      userId,
      name,
      keyBundle,
      Timestamp.now()
    );
  }

  get id(): DeviceId { return this._id; }
  get userId(): UserId { return this._userId; }
  get name(): string { return this._name; }
  get keyBundle(): CryptoKeyBundle { return this._keyBundle; }
  get registrationTimestamp(): Timestamp { return this._registrationTimestamp; }
  get isActive(): boolean { return this._isActive; }
  get lastSeenTimestamp(): Timestamp | undefined { return this._lastSeenTimestamp; }

  deactivate(): void {
    this._isActive = false;
  }

  activate(): void {
    this._isActive = true;
  }

  updateLastSeen(): void {
    this._lastSeenTimestamp = Timestamp.now();
  }

  isOwnedBy(userId: UserId): boolean {
    return this._userId.equals(userId);
  }
}

/**
 * Represents a user in the encrypted chat system with device management capabilities
 */
export class User {
  private readonly _devices: Map<string, Device> = new Map();

  private constructor(
    private readonly _id: UserId,
    private readonly _email: Email,
    private readonly _createdAt: Timestamp,
    private _isVerified: boolean = false
  ) {}

  static create(id: UserId, email: Email): User {
    return new User(id, email, Timestamp.now());
  }

  get id(): UserId { return this._id; }
  get email(): Email { return this._email; }
  get createdAt(): Timestamp { return this._createdAt; }
  get isVerified(): boolean { return this._isVerified; }
  get devices(): ReadonlyArray<Device> { return Array.from(this._devices.values()); }

  addDevice(device: Device): void {
    if (!device.isOwnedBy(this._id)) {
      throw new Error('Device does not belong to this user');
    }

    if (this._devices.has(device.id.value)) {
      throw new Error('Device already exists for this user');
    }

    this._devices.set(device.id.value, device);
  }

  removeDevice(deviceId: DeviceId): void {
    const device = this._devices.get(deviceId.value);
    if (!device) {
      throw new Error('Device not found');
    }

    device.deactivate();
    this._devices.delete(deviceId.value);
  }

  getDevice(deviceId: DeviceId): Device | undefined {
    return this._devices.get(deviceId.value);
  }

  getActiveDevices(): ReadonlyArray<Device> {
    return this.devices.filter(device => device.isActive);
  }

  verify(): void {
    this._isVerified = true;
  }

  hasMaxDevices(maxDevices: number = 10): boolean {
    return this.devices.length >= maxDevices;
  }
}

/**
 * Represents an encrypted message with all necessary cryptographic components
 */
export class EncryptedMessage {
  private constructor(
    private readonly _id: MessageId,
    private readonly _senderId: UserId,
    private readonly _senderDeviceId: DeviceId,
    private readonly _recipientId: UserId,
    private readonly _recipientDeviceId: DeviceId,
    private readonly _sessionId: SessionId,
    private readonly _cipherText: CipherText,
    private readonly _nonce: Nonce,
    private readonly _authTag: AuthenticationTag,
    private readonly _timestamp: Timestamp,
    private readonly _messageNumber: number,
    private _isDelivered: boolean = false,
    private _isRead: boolean = false,
    private _deliveredAt?: Timestamp,
    private _readAt?: Timestamp
  ) {}

  static create(
    id: MessageId,
    senderId: UserId,
    senderDeviceId: DeviceId,
    recipientId: UserId,
    recipientDeviceId: DeviceId,
    sessionId: SessionId,
    cipherText: CipherText,
    nonce: Nonce,
    authTag: AuthenticationTag,
    messageNumber: number
  ): EncryptedMessage {
    if (messageNumber < 0) {
      throw new Error('Message number must be non-negative');
    }

    return new EncryptedMessage(
      id,
      senderId,
      senderDeviceId,
      recipientId,
      recipientDeviceId,
      sessionId,
      cipherText,
      nonce,
      authTag,
      Timestamp.now(),
      messageNumber
    );
  }

  get id(): MessageId { return this._id; }
  get senderId(): UserId { return this._senderId; }
  get senderDeviceId(): DeviceId { return this._senderDeviceId; }
  get recipientId(): UserId { return this._recipientId; }
  get recipientDeviceId(): DeviceId { return this._recipientDeviceId; }
  get sessionId(): SessionId { return this._sessionId; }
  get cipherText(): CipherText { return this._cipherText; }
  get nonce(): Nonce { return this._nonce; }
  get authTag(): AuthenticationTag { return this._authTag; }
  get timestamp(): Timestamp { return this._timestamp; }
  get messageNumber(): number { return this._messageNumber; }
  get isDelivered(): boolean { return this._isDelivered; }
  get isRead(): boolean { return this._isRead; }
  get deliveredAt(): Timestamp | undefined { return this._deliveredAt; }
  get readAt(): Timestamp | undefined { return this._readAt; }

  markAsDelivered(): void {
    if (this._isDelivered) {
      throw new Error('Message already marked as delivered');
    }
    this._isDelivered = true;
    this._deliveredAt = Timestamp.now();
  }

  markAsRead(): void {
    if (!this._isDelivered) {
      throw new Error('Cannot mark undelivered message as read');
    }
    if (this._isRead) {
      throw new Error('Message already marked as read');
    }
    this._isRead = true;
    this._readAt = Timestamp.now();
  }

  isSentBy(userId: UserId, deviceId: DeviceId): boolean {
    return this._senderId.equals(userId) && this._senderDeviceId.equals(deviceId);
  }

  isReceivedBy(userId: UserId, deviceId: DeviceId): boolean {
    return this._recipientId.equals(userId) && this._recipientDeviceId.equals(deviceId);
  }
}

/**
 * Double Ratchet state for maintaining forward secrecy
 */
export interface DoubleRatchetState {
  readonly rootKey: CryptoKey;
  readonly sendingChainKey: CryptoKey;
  readonly receivingChainKey: CryptoKey;
  readonly dhSendingKey: CryptoKey;
  readonly dhReceivingKey: CryptoKey;
  readonly sendingMessageNumber: number;
  readonly receivingMessageNumber: number;
  readonly previousSendingChainLength: number;
  readonly skippedMessageKeys: ReadonlyMap<number, CryptoKey>;
}

/**
 * Represents a chat session with Double Ratchet encryption state
 */
export class ChatSession {
  private _messages: Map<string, EncryptedMessage> = new Map();

  private constructor(
    private readonly _id: SessionId,
    private readonly _participantAId: UserId,
    private readonly _participantADeviceId: DeviceId,
    private readonly _participantBId: UserId,
    private readonly _participantBDeviceId: DeviceId,
    private readonly _createdAt: Timestamp,
    private _ratchetState: DoubleRatchetState,
    private _isActive: boolean = true,
    private _lastActivityAt?: Timestamp
  ) {}

  static create(
    id: SessionId,
    participantAId: UserId,
    participantADeviceId: DeviceId,
    participantBId: UserId,
    participantBDeviceId: DeviceId,
    initialRatchetState: DoubleRatchetState
  ): ChatSession {
    if (participantAId.equals(participantBId) && participantADeviceId.equals(participantBDeviceId)) {
      throw new Error('Cannot create session with same participant and device');
    }

    return new ChatSession(
      id,
      participantAId,
      participantADeviceId,
      participantBId,
      participantBDeviceId,
      Timestamp.now(),
      initialRatchetState
    );
  }

  get id(): SessionId { return this._id; }
  get participantAId(): UserId { return this._participantAId; }
  get participantADeviceId(): DeviceId { return this._participantADeviceId; }
  get participantBId(): UserId { return this._participantBId; }
  get participantBDeviceId(): DeviceId { return this._participantBDeviceId; }
  get createdAt(): Timestamp { return this._createdAt; }
  get ratchetState(): DoubleRatchetState { return this._ratchetState; }
  get isActive(): boolean { return this._isActive; }
  get lastActivityAt(): Timestamp | undefined { return this._lastActivityAt; }
  get messages(): ReadonlyArray<EncryptedMessage> { return Array.from(this._messages.values()); }

  addMessage(message: EncryptedMessage): void {
    if (!this.isParticipant(message.senderId, message.senderDeviceId) ||
        !this.isParticipant(message.recipientId, message.recipientDeviceId)) {
      throw new Error('Message participants do not match session participants');
    }

    if (!message.sessionId.equals(this._id)) {
      throw new Error('Message session ID does not match this session');
    }

    if (this._messages.has(message.id.value)) {
      throw new Error('Message already exists in this session');
    }

    this._messages.set(message.id.value, message);
    this._lastActivityAt = Timestamp.now();
  }

  getMessage(messageId: MessageId): EncryptedMessage | undefined {
    return this._messages.get(messageId.value);
  }

  updateRatchetState(newState: DoubleRatchetState): void {
    if (!this._isActive) {
      throw new Error('Cannot update ratchet state for inactive session');
    }
    this._ratchetState = newState;
  }

  isParticipant(userId: UserId, deviceId: DeviceId): boolean {
    return (this._participantAId.equals(userId) && this._participantADeviceId.equals(deviceId)) ||
           (this._participantBId.equals(userId) && this._participantBDeviceId.equals(deviceId));
  }

  getOtherParticipant(userId: UserId, deviceId: DeviceId): { userId: UserId; deviceId: DeviceId } | undefined {
    if (this._participantAId.equals(userId) && this._participantADeviceId.equals(deviceId)) {
      return { userId: this._participantBId, deviceId: this._participantBDeviceId };
    }
    if (this._participantBId.equals(userId) && this._participantBDeviceId.equals(deviceId)) {
      return { userId: this._participantAId, deviceId: this._participantADeviceId };
    }
    return undefined;
  }

  deactivate(): void {
    this._isActive = false;
  }

  getMessagesAfter(timestamp: Timestamp): ReadonlyArray<EncryptedMessage> {
    return this.messages.filter(msg => msg.timestamp.isAfter(timestamp));
  }

  getUndeliveredMessages(recipientId: UserId, recipientDeviceId: DeviceId): ReadonlyArray<EncryptedMessage> {
    return this.messages.filter(msg => 
      msg.isReceivedBy(recipientId, recipientDeviceId) && !msg.isDelivered
    );
  }
}

/**
 * Security verification status and methods
 */
export enum VerificationStatus {
  UNVERIFIED = 'unverified',
  VERIFIED = 'verified',
  COMPROMISED = 'compromised'
}

/**
 * Represents security verification between two users
 */
export class SecurityVerification {
  private constructor(
    private readonly _userAId: UserId,
    private readonly _userBId: UserId,
    private readonly _securityNumber: SecurityNumber,
    private readonly _createdAt: Timestamp,
    private _status: VerificationStatus = VerificationStatus.UNVERIFIED,
    private _verifiedAt?: Timestamp,
    private _verifiedByUserA: boolean = false,
    private _verifiedByUserB: boolean = false
  ) {}

  static create(
    userAId: UserId,
    userBId: UserId,
    securityNumber: SecurityNumber
  ): SecurityVerification {
    if (userAId.equals(userBId)) {
      throw new Error('Cannot create verification between same user');
    }

    return new SecurityVerification(
      userAId,
      userBId,
      securityNumber,
      Timestamp.now()
    );
  }

  get userAId(): UserId { return this._userAId; }
  get userBId(): UserId { return this._userBId; }
  get securityNumber(): SecurityNumber { return this._securityNumber; }
  get createdAt(): Timestamp { return this._createdAt; }
  get status(): VerificationStatus { return this._status; }
  get verifiedAt(): Timestamp | undefined { return this._verifiedAt; }
  get isVerifiedByUserA(): boolean { return this._verifiedByUserA; }
  get isVerifiedByUserB(): boolean { return this._verifiedByUserB; }

  verifyByUser(userId: UserId): void {
    if (!this.involvesUser(userId)) {
      throw new Error('User is not part of this verification');
    }

    if (this._status === VerificationStatus.COMPROMISED) {
      throw new Error('Cannot verify compromised security verification');
    }

    if (this._userAId.equals(userId)) {
      this._verifiedByUserA = true;
    } else if (this._userBId.equals(userId)) {
      this._verifiedByUserB = true;
    }

    // Mark as verified if both users have verified
    if (this._verifiedByUserA && this._verifiedByUserB && this._status === VerificationStatus.UNVERIFIED) {
      this._status = VerificationStatus.VERIFIED;
      this._verifiedAt = Timestamp.now();
    }
  }

  markAsCompromised(): void {
    this._status = VerificationStatus.COMPROMISED;
    this._verifiedByUserA = false;
    this._verifiedByUserB = false;
    this._verifiedAt = undefined;
  }

  involvesUser(userId: UserId): boolean {
    return this._userAId.equals(userId) || this._userBId.equals(userId);
  }

  getOtherUser(userId: UserId): UserId | undefined {
    if (this._userAId.equals(userId)) {
      return this._userBId;
    }
    if (this._userBId.equals(userId)) {
      return this._userAId;
    }
    return undefined;
  }

  isFullyVerified(): boolean {
    return this._status === VerificationStatus.VERIFIED && 
           this._verifiedByUserA && 
           this._verifiedByUserB;
  }
}