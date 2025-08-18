/**
 * Domain Services for E2E Encrypted Chat Application - Phase 5
 * 
 * This file contains domain services that encapsulate business logic
 * that doesn't naturally fit within entities or value objects.
 */

import {
  User,
  Device,
  EncryptedMessage,
  ChatSession,
  SecurityVerification,
  VerificationStatus,
  CryptoKeyBundle,
  DoubleRatchetState
} from './entities';
import {
  UserId,
  DeviceId,
  SessionId,
  MessageId,
  CipherText,
  Nonce,
  AuthenticationTag,
  SecurityNumber,
  Timestamp
} from './value-objects';

/**
 * Domain events for the chat system
 */
export interface DomainEvent {
  readonly eventId: string;
  readonly timestamp: Timestamp;
  readonly aggregateId: string;
}

export interface MessageEncryptedEvent extends DomainEvent {
  readonly messageId: MessageId;
  readonly senderId: UserId;
  readonly recipientId: UserId;
  readonly sessionId: SessionId;
}

export interface KeyRotatedEvent extends DomainEvent {
  readonly userId: UserId;
  readonly deviceId: DeviceId;
  readonly keyType: 'identity' | 'ephemeral' | 'preKey' | 'signedPreKey';
}

export interface SessionEstablishedEvent extends DomainEvent {
  readonly sessionId: SessionId;
  readonly participantAId: UserId;
  readonly participantBId: UserId;
}

/**
 * Result types for service operations
 */
export interface EncryptionResult {
  readonly cipherText: CipherText;
  readonly nonce: Nonce;
  readonly authTag: AuthenticationTag;
  readonly updatedRatchetState: DoubleRatchetState;
}

export interface DecryptionResult {
  readonly plaintext: string;
  readonly updatedRatchetState: DoubleRatchetState;
}

export interface KeyGenerationResult {
  readonly keyBundle: CryptoKeyBundle;
  readonly publicKeyBundle: PublicKeyBundle;
}

export interface PublicKeyBundle {
  readonly identityPublicKey: ArrayBuffer;
  readonly ephemeralPublicKey: ArrayBuffer;
  readonly preKeyPublicKeys: ReadonlyArray<ArrayBuffer>;
  readonly signedPreKeyPublic: {
    readonly key: ArrayBuffer;
    readonly signature: ArrayBuffer;
    readonly timestamp: Timestamp;
  };
}

/**
 * Service for handling cryptographic operations
 */
export interface IEncryptionService {
  /**
   * Encrypts a message using Double Ratchet algorithm
   */
  encryptMessage(
    plaintext: string,
    session: ChatSession,
    sendingDeviceId: DeviceId
  ): Promise<EncryptionResult>;

  /**
   * Decrypts a message using Double Ratchet algorithm
   */
  decryptMessage(
    message: EncryptedMessage,
    session: ChatSession,
    receivingDeviceId: DeviceId
  ): Promise<DecryptionResult>;

  /**
   * Generates a new key bundle for a device
   */
  generateKeyBundle(deviceId: DeviceId): Promise<KeyGenerationResult>;

  /**
   * Derives a shared secret from two key bundles
   */
  deriveSharedSecret(
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle
  ): Promise<ArrayBuffer>;

  /**
   * Initializes Double Ratchet state for a new session
   */
  initializeDoubleRatchet(
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle,
    isInitiator: boolean
  ): Promise<DoubleRatchetState>;

  /**
   * Rotates keys in the Double Ratchet
   */
  rotateRatchetKeys(currentState: DoubleRatchetState): Promise<DoubleRatchetState>;
}

/**
 * Default implementation of encryption service
 */
export class EncryptionService implements IEncryptionService {
  private readonly algorithm = 'AES-GCM';
  private readonly keyLength = 256;

  async encryptMessage(
    plaintext: string,
    session: ChatSession,
    sendingDeviceId: DeviceId
  ): Promise<EncryptionResult> {
    if (!session.isActive) {
      throw new Error('Cannot encrypt message for inactive session');
    }

    // Generate new symmetric key from ratchet
    const messageKey = await this.deriveMessageKey(
      session.ratchetState,
      session.ratchetState.sendingMessageNumber
    );

    // Encrypt the message
    const encoder = new TextEncoder();
    const data = encoder.encode(plaintext);
    const nonce = Nonce.generate();

    const encrypted = await crypto.subtle.encrypt(
      {
        name: this.algorithm,
        iv: nonce.value
      },
      messageKey,
      data
    );

    // Extract ciphertext and auth tag (last 16 bytes for AES-GCM)
    const cipherTextLength = encrypted.byteLength - 16;
    const cipherText = CipherText.create(encrypted.slice(0, cipherTextLength));
    const authTag = AuthenticationTag.create(encrypted.slice(cipherTextLength));

    // Update ratchet state
    const updatedRatchetState = await this.advanceSendingRatchet(session.ratchetState);

    return {
      cipherText,
      nonce,
      authTag,
      updatedRatchetState
    };
  }

  async decryptMessage(
    message: EncryptedMessage,
    session: ChatSession,
    receivingDeviceId: DeviceId
  ): Promise<DecryptionResult> {
    if (!session.isActive) {
      throw new Error('Cannot decrypt message for inactive session');
    }

    // Derive message key from ratchet
    const messageKey = await this.deriveMessageKey(
      session.ratchetState,
      message.messageNumber
    );

    // Combine ciphertext and auth tag
    const cipherTextArray = new Uint8Array(message.cipherText.value);
    const authTagArray = new Uint8Array(message.authTag.value);
    const combined = new Uint8Array(cipherTextArray.length + authTagArray.length);
    combined.set(cipherTextArray);
    combined.set(authTagArray, cipherTextArray.length);

    try {
      const decrypted = await crypto.subtle.decrypt(
        {
          name: this.algorithm,
          iv: message.nonce.value
        },
        messageKey,
        combined
      );

      const decoder = new TextDecoder();
      const plaintext = decoder.decode(decrypted);

      // Update ratchet state
      const updatedRatchetState = await this.advanceReceivingRatchet(
        session.ratchetState,
        message.messageNumber
      );

      return {
        plaintext,
        updatedRatchetState
      };
    } catch (error) {
      throw new Error('Failed to decrypt message - invalid key or corrupted data');
    }
  }

  async generateKeyBundle(deviceId: DeviceId): Promise<KeyGenerationResult> {
    // Generate identity key (long-term)
    const identityKeyPair = await crypto.subtle.generateKey(
      {
        name: 'ECDH',
        namedCurve: 'P-256'
      },
      true,
      ['deriveKey', 'deriveBits']
    );

    // Generate ephemeral key
    const ephemeralKeyPair = await crypto.subtle.generateKey(
      {
        name: 'ECDH',
        namedCurve: 'P-256'
      },
      true,
      ['deriveKey', 'deriveBits']
    );

    // Generate pre-keys (one-time keys)
    const preKeyPairs = await Promise.all(
      Array.from({ length: 100 }, () =>
        crypto.subtle.generateKey(
          {
            name: 'ECDH',
            namedCurve: 'P-256'
          },
          true,
          ['deriveKey', 'deriveBits']
        )
      )
    );

    // Generate signed pre-key
    const signedPreKeyPair = await crypto.subtle.generateKey(
      {
        name: 'ECDH',
        namedCurve: 'P-256'
      },
      true,
      ['deriveKey', 'deriveBits']
    );

    // Sign the pre-key with identity key
    const signedPreKeyPublic = await crypto.subtle.exportKey('raw', signedPreKeyPair.publicKey);
    const signature = await crypto.subtle.sign(
      { name: 'ECDSA', hash: 'SHA-256' },
      identityKeyPair.privateKey,
      signedPreKeyPublic
    );

    const keyBundle: CryptoKeyBundle = {
      identityKey: identityKeyPair.privateKey,
      ephemeralKey: ephemeralKeyPair.privateKey,
      preKeys: preKeyPairs.map(pair => pair.privateKey),
      signedPreKey: {
        key: signedPreKeyPair.privateKey,
        signature,
        timestamp: Timestamp.now()
      }
    };

    const publicKeyBundle: PublicKeyBundle = {
      identityPublicKey: await crypto.subtle.exportKey('raw', identityKeyPair.publicKey),
      ephemeralPublicKey: await crypto.subtle.exportKey('raw', ephemeralKeyPair.publicKey),
      preKeyPublicKeys: await Promise.all(
        preKeyPairs.map(pair => crypto.subtle.exportKey('raw', pair.publicKey))
      ),
      signedPreKeyPublic: {
        key: signedPreKeyPublic,
        signature,
        timestamp: Timestamp.now()
      }
    };

    return { keyBundle, publicKeyBundle };
  }

  async deriveSharedSecret(
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle
  ): Promise<ArrayBuffer> {
    // Implement X3DH key agreement protocol
    const remoteIdentityKey = await crypto.subtle.importKey(
      'raw',
      remotePublicKeyBundle.identityPublicKey,
      { name: 'ECDH', namedCurve: 'P-256' },
      false,
      []
    );

    const sharedSecret = await crypto.subtle.deriveBits(
      { name: 'ECDH', public: remoteIdentityKey },
      localKeyBundle.identityKey,
      256
    );

    return sharedSecret;
  }

  async initializeDoubleRatchet(
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle,
    isInitiator: boolean
  ): Promise<DoubleRatchetState> {
    // Derive root key from shared secret
    const sharedSecret = await this.deriveSharedSecret(localKeyBundle, remotePublicKeyBundle);
    const rootKey = await this.importKey(sharedSecret);

    // Initialize chain keys
    const sendingChainKey = await this.deriveChainKey(rootKey, 'sending');
    const receivingChainKey = await this.deriveChainKey(rootKey, 'receiving');

    return {
      rootKey,
      sendingChainKey,
      receivingChainKey,
      dhSendingKey: localKeyBundle.ephemeralKey,
      dhReceivingKey: await this.importPublicKey(remotePublicKeyBundle.ephemeralPublicKey),
      sendingMessageNumber: 0,
      receivingMessageNumber: 0,
      previousSendingChainLength: 0,
      skippedMessageKeys: new Map()
    };
  }

  async rotateRatchetKeys(currentState: DoubleRatchetState): Promise<DoubleRatchetState> {
    // Generate new DH key pair
    const newDHKeyPair = await crypto.subtle.generateKey(
      {
        name: 'ECDH',
        namedCurve: 'P-256'
      },
      true,
      ['deriveKey', 'deriveBits']
    );

    // Perform DH ratchet step
    const newSharedSecret = await crypto.subtle.deriveBits(
      { name: 'ECDH', public: currentState.dhReceivingKey },
      newDHKeyPair.privateKey,
      256
    );

    const newRootKey = await this.importKey(newSharedSecret);
    const newSendingChainKey = await this.deriveChainKey(newRootKey, 'sending');

    return {
      ...currentState,
      rootKey: newRootKey,
      sendingChainKey: newSendingChainKey,
      dhSendingKey: newDHKeyPair.privateKey,
      previousSendingChainLength: currentState.sendingMessageNumber,
      sendingMessageNumber: 0
    };
  }

  private async deriveMessageKey(
    ratchetState: DoubleRatchetState,
    messageNumber: number
  ): Promise<CryptoKey> {
    const keyMaterial = await crypto.subtle.deriveBits(
      { name: 'HKDF', hash: 'SHA-256', salt: new ArrayBuffer(0), info: new TextEncoder().encode(`message-${messageNumber}`) },
      ratchetState.sendingChainKey,
      256
    );

    return await crypto.subtle.importKey(
      'raw',
      keyMaterial,
      { name: this.algorithm },
      false,
      ['encrypt', 'decrypt']
    );
  }

  private async advanceSendingRatchet(currentState: DoubleRatchetState): Promise<DoubleRatchetState> {
    const newChainKey = await this.deriveChainKey(currentState.rootKey, 'sending-next');
    
    return {
      ...currentState,
      sendingChainKey: newChainKey,
      sendingMessageNumber: currentState.sendingMessageNumber + 1
    };
  }

  private async advanceReceivingRatchet(
    currentState: DoubleRatchetState,
    messageNumber: number
  ): Promise<DoubleRatchetState> {
    if (messageNumber <= currentState.receivingMessageNumber) {
      // Handle out-of-order message
      return currentState;
    }

    const newChainKey = await this.deriveChainKey(currentState.rootKey, 'receiving-next');
    
    return {
      ...currentState,
      receivingChainKey: newChainKey,
      receivingMessageNumber: messageNumber
    };
  }

  private async deriveChainKey(rootKey: CryptoKey, context: string): Promise<CryptoKey> {
    const keyMaterial = await crypto.subtle.deriveBits(
      { name: 'HKDF', hash: 'SHA-256', salt: new ArrayBuffer(0), info: new TextEncoder().encode(context) },
      rootKey,
      256
    );

    return await crypto.subtle.importKey(
      'raw',
      keyMaterial,
      { name: 'HKDF' },
      false,
      ['deriveKey', 'deriveBits']
    );
  }

  private async importKey(keyMaterial: ArrayBuffer): Promise<CryptoKey> {
    return await crypto.subtle.importKey(
      'raw',
      keyMaterial,
      { name: 'HKDF' },
      false,
      ['deriveKey', 'deriveBits']
    );
  }

  private async importPublicKey(keyData: ArrayBuffer): Promise<CryptoKey> {
    return await crypto.subtle.importKey(
      'raw',
      keyData,
      { name: 'ECDH', namedCurve: 'P-256' },
      false,
      []
    );
  }
}

/**
 * Service for managing cryptographic keys lifecycle
 */
export interface IKeyManagementService {
  rotateKeys(userId: UserId, deviceId: DeviceId): Promise<void>;
  revokeDevice(userId: UserId, deviceId: DeviceId): Promise<void>;
  generatePreKeys(deviceId: DeviceId, count: number): Promise<CryptoKeyBundle>;
  validateKeyBundle(keyBundle: CryptoKeyBundle): Promise<boolean>;
}

export class KeyManagementService implements IKeyManagementService {
  constructor(
    private readonly encryptionService: IEncryptionService,
    private readonly eventPublisher: (event: DomainEvent) => void
  ) {}

  async rotateKeys(userId: UserId, deviceId: DeviceId): Promise<void> {
    // Generate new key bundle
    const { keyBundle } = await this.encryptionService.generateKeyBundle(deviceId);
    
    // Publish key rotation event
    this.eventPublisher({
      eventId: MessageId.generate().value,
      timestamp: Timestamp.now(),
      aggregateId: userId.value,
      userId,
      deviceId,
      keyType: 'identity'
    } as KeyRotatedEvent);
  }

  async revokeDevice(userId: UserId, deviceId: DeviceId): Promise<void> {
    // Mark device as revoked and rotate all keys
    await this.rotateKeys(userId, deviceId);
  }

  async generatePreKeys(deviceId: DeviceId, count: number): Promise<CryptoKeyBundle> {
    if (count <= 0 || count > 1000) {
      throw new Error('Pre-key count must be between 1 and 1000');
    }

    const { keyBundle } = await this.encryptionService.generateKeyBundle(deviceId);
    return keyBundle;
  }

  async validateKeyBundle(keyBundle: CryptoKeyBundle): Promise<boolean> {
    try {
      // Validate identity key
      if (!keyBundle.identityKey) return false;
      
      // Validate ephemeral key
      if (!keyBundle.ephemeralKey) return false;
      
      // Validate pre-keys
      if (!keyBundle.preKeys || keyBundle.preKeys.length === 0) return false;
      
      // Validate signed pre-key
      if (!keyBundle.signedPreKey || !keyBundle.signedPreKey.key || !keyBundle.signedPreKey.signature) {
        return false;
      }
      
      return true;
    } catch {
      return false;
    }
  }
}

/**
 * Service for managing chat sessions
 */
export interface ISessionService {
  createSession(
    participantAId: UserId,
    participantADeviceId: DeviceId,
    participantBId: UserId,
    participantBDeviceId: DeviceId,
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle
  ): Promise<ChatSession>;
  
  terminateSession(sessionId: SessionId): Promise<void>;
  validateSessionIntegrity(session: ChatSession): Promise<boolean>;
}

export class SessionService implements ISessionService {
  constructor(
    private readonly encryptionService: IEncryptionService,
    private readonly eventPublisher: (event: DomainEvent) => void
  ) {}

  async createSession(
    participantAId: UserId,
    participantADeviceId: DeviceId,
    participantBId: UserId,
    participantBDeviceId: DeviceId,
    localKeyBundle: CryptoKeyBundle,
    remotePublicKeyBundle: PublicKeyBundle
  ): Promise<ChatSession> {
    const sessionId = SessionId.generate();
    
    const ratchetState = await this.encryptionService.initializeDoubleRatchet(
      localKeyBundle,
      remotePublicKeyBundle,
      true // Assume first participant is initiator
    );

    const session = ChatSession.create(
      sessionId,
      participantAId,
      participantADeviceId,
      participantBId,
      participantBDeviceId,
      ratchetState
    );

    // Publish session established event
    this.eventPublisher({
      eventId: MessageId.generate().value,
      timestamp: Timestamp.now(),
      aggregateId: sessionId.value,
      sessionId,
      participantAId,
      participantBId
    } as SessionEstablishedEvent);

    return session;
  }

  async terminateSession(sessionId: SessionId): Promise<void> {
    // Session termination logic would be handled by the aggregate
    // This service might clean up any external resources
  }

  async validateSessionIntegrity(session: ChatSession): Promise<boolean> {
    // Validate session state and ratchet integrity
    return session.isActive && 
           session.ratchetState.sendingMessageNumber >= 0 &&
           session.ratchetState.receivingMessageNumber >= 0;
  }
}

/**
 * Service for security verification between users
 */
export interface IVerificationService {
  initiateVerification(userAId: UserId, userBId: UserId): Promise<SecurityVerification>;
  generateSecurityNumber(userAId: UserId, userBId: UserId): Promise<SecurityNumber>;
  verifySecurityNumber(
    verification: SecurityVerification, 
    providedNumber: SecurityNumber,
    verifyingUserId: UserId
  ): Promise<boolean>;
  markAsCompromised(verification: SecurityVerification): Promise<void>;
}

export class VerificationService implements IVerificationService {
  async initiateVerification(userAId: UserId, userBId: UserId): Promise<SecurityVerification> {
    const securityNumber = await this.generateSecurityNumber(userAId, userBId);
    return SecurityVerification.create(userAId, userBId, securityNumber);
  }

  async generateSecurityNumber(userAId: UserId, userBId: UserId): Promise<SecurityNumber> {
    // In practice, this would be derived from the users' identity keys
    // For now, generate a random security number
    return SecurityNumber.generate();
  }

  async verifySecurityNumber(
    verification: SecurityVerification,
    providedNumber: SecurityNumber,
    verifyingUserId: UserId
  ): Promise<boolean> {
    if (!verification.involvesUser(verifyingUserId)) {
      throw new Error('User is not part of this verification');
    }

    const isValid = verification.securityNumber.equals(providedNumber);
    
    if (isValid) {
      verification.verifyByUser(verifyingUserId);
    }

    return isValid;
  }

  async markAsCompromised(verification: SecurityVerification): Promise<void> {
    verification.markAsCompromised();
  }
}

/**
 * Service for handling message delivery
 */
export interface IMessageDeliveryService {
  deliverMessage(message: EncryptedMessage): Promise<boolean>;
  markMessageAsDelivered(messageId: MessageId): Promise<void>;
  markMessageAsRead(messageId: MessageId): Promise<void>;
  getUndeliveredMessages(userId: UserId, deviceId: DeviceId): Promise<EncryptedMessage[]>;
}

export class MessageDeliveryService implements IMessageDeliveryService {
  constructor(private readonly eventPublisher: (event: DomainEvent) => void) {}

  async deliverMessage(message: EncryptedMessage): Promise<boolean> {
    try {
      // Implementation would interface with message transport layer
      // For now, simulate successful delivery
      message.markAsDelivered();
      
      // Publish message encrypted event
      this.eventPublisher({
        eventId: MessageId.generate().value,
        timestamp: Timestamp.now(),
        aggregateId: message.sessionId.value,
        messageId: message.id,
        senderId: message.senderId,
        recipientId: message.recipientId,
        sessionId: message.sessionId
      } as MessageEncryptedEvent);

      return true;
    } catch {
      return false;
    }
  }

  async markMessageAsDelivered(messageId: MessageId): Promise<void> {
    // This would typically update the message in a repository
    // Implementation depends on the infrastructure layer
  }

  async markMessageAsRead(messageId: MessageId): Promise<void> {
    // This would typically update the message in a repository
    // Implementation depends on the infrastructure layer
  }

  async getUndeliveredMessages(userId: UserId, deviceId: DeviceId): Promise<EncryptedMessage[]> {
    // This would query the repository for undelivered messages
    // Implementation depends on the infrastructure layer
    return [];
  }
}