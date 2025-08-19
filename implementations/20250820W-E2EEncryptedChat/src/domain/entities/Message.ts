import { UserId } from './User';
import { EphemeralKey } from './CryptoKey';

export type MessageId = string;

export interface CipherText {
  value: Uint8Array;
}

export interface Nonce {
  value: Uint8Array;
}

export interface AuthenticationTag {
  value: Uint8Array;
}

export interface EncryptedMessage {
  id: MessageId;
  senderId: UserId;
  recipientId: UserId;
  ciphertext: CipherText;
  nonce: Nonce;
  authTag: AuthenticationTag;
  timestamp: Date;
  ephemeralKey?: EphemeralKey;
}

export interface PlainMessage {
  id: MessageId;
  senderId: UserId;
  recipientId: UserId;
  content: string;
  timestamp: Date;
  status: MessageStatus;
}

export enum MessageStatus {
  SENDING = 'sending',
  SENT = 'sent',
  DELIVERED = 'delivered',
  READ = 'read',
  FAILED = 'failed'
}