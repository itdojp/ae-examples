import { v4 as uuidv4 } from 'uuid';
import { 
  Message, 
  SessionNotFoundError,
  DecryptionError 
} from '../entities';
import { SessionService } from './sessionService';
import { MessageRepository } from '../../infra/repositories/messageRepository';
import { SessionRepository } from '../../infra/repositories/sessionRepository';
import { DoubleRatchet } from '../crypto/doubleRatchet';
import { Database } from '../../infra/db';
import sodium from 'libsodium-wrappers';

export interface MessageService {
  sendMessage(senderId: string, recipientId: string, content: string): Promise<Message>;
  receiveMessage(messageId: string, recipientId: string): Promise<string>;
  getMessages(userId: string, peerId: string, limit?: number, offset?: number): Promise<Message[]>;
  markAsDelivered(messageId: string): Promise<void>;
  markAsRead(messageId: string): Promise<void>;
  deleteMessage(messageId: string, userId: string): Promise<void>;
}

export class MessageServiceImpl implements MessageService {
  private sessionService: SessionService;
  private messageRepository: MessageRepository;
  private sessionRepository: SessionRepository;
  
  constructor(
    private db: Database,
    sessionService: SessionService,
    messageRepository: MessageRepository,
    sessionRepository: SessionRepository
  ) {
    this.sessionService = sessionService;
    this.messageRepository = messageRepository;
    this.sessionRepository = sessionRepository;
  }

  async initialize() {
    await DoubleRatchet.initialize();
  }

  async sendMessage(senderId: string, recipientId: string, content: string): Promise<Message> {
    // Get or establish session
    let session = await this.sessionService.getSession(senderId, recipientId);
    if (!session) {
      session = await this.sessionService.establishSession(senderId, recipientId);
    }

    // Reconstruct Double Ratchet state from session
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

    // Encrypt message
    const plaintext = new TextEncoder().encode(content);
    const { header, ciphertext } = await doubleRatchet.ratchetEncrypt(plaintext);

    // Extract nonce and auth tag from ciphertext
    const nonce = ciphertext.slice(0, sodium.crypto_secretbox_NONCEBYTES);
    const actualCiphertext = ciphertext.slice(sodium.crypto_secretbox_NONCEBYTES);
    
    // Create message record
    const message: Message = {
      id: uuidv4(),
      senderId,
      recipientId,
      sessionId: session.id,
      ciphertext: sodium.to_base64(actualCiphertext),
      nonce: sodium.to_base64(nonce),
      authTag: '', // Auth tag is included in ciphertext for secretbox
      dhPublicKey: header.dhPublicKey,
      messageNumber: header.messageNumber,
      previousChainLength: header.previousChainLength,
      timestamp: new Date(),
      delivered: false,
      read: false
    };

    // Save message to database
    await this.messageRepository.save(message);

    // Update session state
    const newState = doubleRatchet.exportState();
    session.sendingMessageNumber = newState.Ns;
    session.receivingMessageNumber = newState.Nr;
    session.previousSendingChainLength = newState.PN;
    session.rootKey = newState.RK;
    session.sendingChainKey = newState.CKs || session.sendingChainKey;
    session.receivingChainKey = newState.CKr || session.receivingChainKey;
    
    if (newState.DHs) {
      session.dhSendingKeyPair = {
        publicKey: newState.DHs.publicKey,
        privateKey: newState.DHs.privateKey
      };
    }
    
    if (newState.DHr) {
      session.dhReceivingKey = newState.DHr;
    }

    await this.sessionService.updateSession(session);

    return message;
  }

  async receiveMessage(messageId: string, recipientId: string): Promise<string> {
    // Get message from database
    const message = await this.messageRepository.findById(messageId);
    if (!message) {
      throw new Error('Message not found');
    }

    if (message.recipientId !== recipientId) {
      throw new Error('Unauthorized');
    }

    // Get session
    const session = await this.sessionRepository.findById(message.sessionId);
    if (!session) {
      throw new SessionNotFoundError(recipientId, message.senderId);
    }

    // Get skipped message keys if any
    const skippedKey = await this.sessionRepository.getSkippedMessageKey(
      session.id,
      message.dhPublicKey || '',
      message.messageNumber
    );

    if (skippedKey) {
      // Use skipped key to decrypt
      const ciphertext = sodium.from_base64(message.ciphertext);
      const nonce = sodium.from_base64(message.nonce);
      const key = sodium.from_base64(skippedKey);
      
      try {
        const plaintext = sodium.crypto_secretbox_open_easy(ciphertext, nonce, key);
        
        // Delete used skipped key
        await this.sessionRepository.deleteSkippedMessageKey(
          session.id,
          message.dhPublicKey || '',
          message.messageNumber
        );
        
        return new TextDecoder().decode(plaintext);
      } catch (error) {
        throw new DecryptionError('Failed to decrypt message with skipped key');
      }
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

    // Reconstruct ciphertext with nonce
    const nonce = sodium.from_base64(message.nonce);
    const actualCiphertext = sodium.from_base64(message.ciphertext);
    const combined = new Uint8Array(nonce.length + actualCiphertext.length);
    combined.set(nonce);
    combined.set(actualCiphertext, nonce.length);

    // Decrypt message
    try {
      const plaintext = await doubleRatchet.ratchetDecrypt(
        {
          dhPublicKey: message.dhPublicKey || '',
          messageNumber: message.messageNumber,
          previousChainLength: message.previousChainLength
        },
        combined
      );

      // Update session state
      const newState = doubleRatchet.exportState();
      session.sendingMessageNumber = newState.Ns;
      session.receivingMessageNumber = newState.Nr;
      session.previousSendingChainLength = newState.PN;
      session.rootKey = newState.RK;
      session.sendingChainKey = newState.CKs || session.sendingChainKey;
      session.receivingChainKey = newState.CKr || session.receivingChainKey;
      
      await this.sessionService.updateSession(session);

      // Mark message as delivered
      await this.markAsDelivered(messageId);

      return new TextDecoder().decode(plaintext);
    } catch (error) {
      throw new DecryptionError(`Failed to decrypt message: ${error}`);
    }
  }

  async getMessages(userId: string, peerId: string, limit = 50, offset = 0): Promise<Message[]> {
    return await this.messageRepository.findBetweenUsers(userId, peerId, limit, offset);
  }

  async markAsDelivered(messageId: string): Promise<void> {
    await this.messageRepository.markAsDelivered(messageId);
  }

  async markAsRead(messageId: string): Promise<void> {
    await this.messageRepository.markAsRead(messageId);
  }

  async deleteMessage(messageId: string, userId: string): Promise<void> {
    // Verify user owns the message
    const message = await this.messageRepository.findById(messageId);
    if (!message) {
      throw new Error('Message not found');
    }

    if (message.senderId !== userId && message.recipientId !== userId) {
      throw new Error('Unauthorized');
    }

    await this.messageRepository.delete(messageId);
  }
}