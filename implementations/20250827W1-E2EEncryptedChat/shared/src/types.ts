export interface User {
  id: string;
  email: string;
  displayName: string;
  publicKey?: string;
  createdAt: Date;
}

export interface Message {
  id: string;
  senderId: string;
  recipientId: string;
  content: string;
  timestamp: Date;
  encrypted: boolean;
  nonce?: string;
  ephemeralKey?: string;
}

export interface EncryptedMessage {
  id: string;
  senderId: string;
  recipientId: string;
  ciphertext: string;
  nonce: string;
  authTag: string;
  timestamp: Date;
  ephemeralKey?: string;
}

export interface KeyPair {
  publicKey: string;
  privateKey: string;
}

export interface ChatSession {
  id: string;
  participants: string[];
  verified: boolean;
  createdAt: Date;
}

export interface SecurityNumber {
  localFingerprint: string;
  remoteFingerprint: string;
}

export type MessageEvent = 
  | { type: 'message'; data: EncryptedMessage }
  | { type: 'typing'; data: { userId: string; isTyping: boolean } }
  | { type: 'presence'; data: { userId: string; status: 'online' | 'offline' } }
  | { type: 'session_verified'; data: { sessionId: string; verified: boolean } };