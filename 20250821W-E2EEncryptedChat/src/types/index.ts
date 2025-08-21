// Core types for E2E Encrypted Chat Application
// Based on ae-framework 6-phase development methodology

export type UserId = string;
export type MessageId = string;
export type SessionId = string;
export type DeviceId = string;

// User domain types
export interface User {
  id: UserId;
  email: string;
  displayName: string;
  createdAt: Date;
  devices: Device[];
  trustLevel: TrustLevel;
}

export interface Device {
  id: DeviceId;
  name: string;
  keyBundle: CryptoKeyBundle;
  lastSeen: Date;
  trusted: boolean;
}

export type TrustLevel = 'untrusted' | 'trusted' | 'verified';

// Cryptographic types
export interface CryptoKeyBundle {
  identityKey: IdentityKey;
  signedPreKey: SignedPreKey;
  oneTimePreKeys: OneTimePreKey[];
  deviceKey: DeviceKey;
}

export interface IdentityKey {
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
}

export interface SignedPreKey {
  id: number;
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
  signature: Uint8Array;
  timestamp: Date;
}

export interface OneTimePreKey {
  id: number;
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
}

export interface DeviceKey {
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
}

export interface EphemeralKey {
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
}

// Message domain types
export interface EncryptedMessage {
  id: MessageId;
  senderId: UserId;
  recipientId: UserId;
  ciphertext: CipherText;
  nonce: Nonce;
  authTag: AuthenticationTag;
  timestamp: Date;
  ephemeralKey?: EphemeralKey;
  messageNumber: number;
  chainKey: Uint8Array;
}

export interface PlainMessage {
  id: MessageId;
  senderId: UserId;
  recipientId: UserId;
  content: string;
  timestamp: Date;
  type: MessageType;
}

export type MessageType = 'text' | 'image' | 'file' | 'system';

// Cryptographic primitives
export class CipherText {
  constructor(private readonly value: Uint8Array) {
    if (value.length < 16) {
      throw new Error("Invalid ciphertext length");
    }
  }
  
  toBase64(): string {
    return btoa(String.fromCharCode(...this.value));
  }
  
  toUint8Array(): Uint8Array {
    return this.value;
  }
}

export class Nonce {
  private static readonly NONCE_LENGTH = 12;
  
  constructor(private readonly value: Uint8Array) {
    if (value.length !== Nonce.NONCE_LENGTH) {
      throw new Error(`Nonce must be ${Nonce.NONCE_LENGTH} bytes`);
    }
  }
  
  static generate(): Nonce {
    const array = new Uint8Array(Nonce.NONCE_LENGTH);
    crypto.getRandomValues(array);
    return new Nonce(array);
  }
  
  toUint8Array(): Uint8Array {
    return this.value;
  }
}

export class AuthenticationTag {
  constructor(private readonly value: Uint8Array) {
    if (value.length !== 16) {
      throw new Error("Authentication tag must be 16 bytes");
    }
  }
  
  toUint8Array(): Uint8Array {
    return this.value;
  }
}

// Session management types
export interface ChatSession {
  id: SessionId;
  participants: UserId[];
  ratchetState: DoubleRatchetState;
  messageKeys: MessageKey[];
  verified: boolean;
  createdAt: Date;
  lastActivity: Date;
}

export interface DoubleRatchetState {
  rootKey: Uint8Array;
  chainKeySend: Uint8Array;
  chainKeyReceive: Uint8Array;
  sendingEphemeralKey: EphemeralKey;
  receivingEphemeralKey?: EphemeralKey;
  sendMessageNumber: number;
  receiveMessageNumber: number;
  previousChainLength: number;
  skippedKeys: Map<string, MessageKey>;
}

export interface MessageKey {
  key: Uint8Array;
  messageNumber: number;
  chainKey: Uint8Array;
}

// Security verification types
export class SecurityNumber {
  constructor(
    private readonly localFingerprint: string,
    private readonly remoteFingerprint: string
  ) {}
  
  verify(other: SecurityNumber): boolean {
    return this.localFingerprint === other.remoteFingerprint &&
           this.remoteFingerprint === other.localFingerprint;
  }
  
  toQRCode(): string {
    return `${this.localFingerprint}:${this.remoteFingerprint}`;
  }
  
  getLocalFingerprint(): string {
    return this.localFingerprint;
  }
  
  getRemoteFingerprint(): string {
    return this.remoteFingerprint;
  }
}

// API types
export interface SendMessageRequest {
  recipientId: UserId;
  content: string;
  sessionId?: SessionId;
}

export interface SendMessageResponse {
  messageId: MessageId;
  sessionId: SessionId;
  timestamp: Date;
}

export interface GetMessagesRequest {
  sessionId: SessionId;
  since?: Date;
  limit?: number;
}

export interface GetMessagesResponse {
  messages: EncryptedMessage[];
  hasMore: boolean;
}

// Event types
export interface DomainEvent {
  id: string;
  type: string;
  timestamp: Date;
  aggregateId: string;
}

export interface MessageSentEvent extends DomainEvent {
  type: 'MessageSent';
  message: EncryptedMessage;
}

export interface SessionEstablishedEvent extends DomainEvent {
  type: 'SessionEstablished';
  session: ChatSession;
}

export interface KeyRotatedEvent extends DomainEvent {
  type: 'KeyRotated';
  userId: UserId;
  keyType: 'identity' | 'signed_pre' | 'one_time_pre';
}

// Error types
export class CryptoError extends Error {
  constructor(message: string, public readonly code: string) {
    super(message);
    this.name = 'CryptoError';
  }
}

export class SessionError extends Error {
  constructor(message: string, public readonly sessionId: SessionId) {
    super(message);
    this.name = 'SessionError';
  }
}

export class KeyError extends Error {
  constructor(message: string, public readonly keyType: string) {
    super(message);
    this.name = 'KeyError';
  }
}