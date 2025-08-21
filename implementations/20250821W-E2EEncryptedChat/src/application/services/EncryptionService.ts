import { CryptoService } from '../../infrastructure/crypto/CryptoService';
import { DoubleRatchet } from '../../infrastructure/crypto/DoubleRatchet';
import { 
  EncryptedMessage, 
  PlainMessage,
  CipherText,
  Nonce,
  AuthenticationTag
} from '../../domain/entities/Message';
import { 
  DoubleRatchetState,
  ChatSession
} from '../../domain/entities/Session';
import { UserId } from '../../domain/entities/User';

export interface EncryptionService {
  encryptMessage(
    plaintext: string,
    recipientKey: Uint8Array,
    sessionState: DoubleRatchetState
  ): Promise<EncryptedMessage>;
  
  decryptMessage(
    encrypted: EncryptedMessage,
    privateKey: Uint8Array,
    sessionState: DoubleRatchetState
  ): Promise<string>;
}

export class E2EEncryptionService implements EncryptionService {
  private cryptoService: CryptoService;
  private doubleRatchet: DoubleRatchet;

  constructor() {
    this.cryptoService = CryptoService.getInstance();
    this.doubleRatchet = new DoubleRatchet();
  }

  async init(): Promise<void> {
    await this.cryptoService.init();
    await this.doubleRatchet.init();
  }

  async encryptMessage(
    plaintext: string,
    recipientKey: Uint8Array,
    sessionState: DoubleRatchetState
  ): Promise<EncryptedMessage> {
    await this.init();
    
    const { ciphertext, header, updatedState } = await this.doubleRatchet.ratchetEncrypt(
      sessionState,
      plaintext
    );
    
    const authTag = await this.cryptoService.generateHMAC(
      sessionState.sendingChainKey,
      ciphertext
    );
    
    const messageId = this.generateMessageId();
    
    return {
      id: messageId,
      senderId: '' as UserId,
      recipientId: '' as UserId,
      ciphertext: { value: ciphertext },
      nonce: { value: header.nonce },
      authTag: { value: authTag },
      timestamp: new Date(),
      ephemeralKey: {
        publicKey: header.publicKey
      }
    };
  }

  async decryptMessage(
    encrypted: EncryptedMessage,
    privateKey: Uint8Array,
    sessionState: DoubleRatchetState
  ): Promise<string> {
    await this.init();
    
    const isValid = await this.cryptoService.verifyHMAC(
      encrypted.authTag.value,
      encrypted.ciphertext.value,
      sessionState.receivingChainKey
    );
    
    if (!isValid) {
      throw new Error('Message authentication failed');
    }
    
    const header = {
      publicKey: encrypted.ephemeralKey!.publicKey,
      previousChainLength: 0,
      messageNumber: 0,
      nonce: encrypted.nonce.value
    };
    
    const { plaintext } = await this.doubleRatchet.ratchetDecrypt(
      sessionState,
      header,
      encrypted.ciphertext.value
    );
    
    return plaintext;
  }

  private generateMessageId(): string {
    return `msg_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }
}