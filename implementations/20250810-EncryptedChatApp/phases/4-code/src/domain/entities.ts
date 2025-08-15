import { z } from 'zod';

// User entity
export const UserSchema = z.object({
  id: z.string().uuid(),
  email: z.string().email(),
  displayName: z.string().min(1).max(100),
  createdAt: z.date(),
  updatedAt: z.date(),
  isVerified: z.boolean(),
  lastSeen: z.date().optional(),
});

export type User = z.infer<typeof UserSchema>;

// Device entity
export const DeviceSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().uuid(),
  deviceFingerprint: z.string(),
  name: z.string().optional(),
  trustLevel: z.enum(['trusted', 'untrusted', 'revoked']),
  createdAt: z.date(),
  lastActivity: z.date(),
});

export type Device = z.infer<typeof DeviceSchema>;

// Identity Key Pair
export const IdentityKeyPairSchema = z.object({
  publicKey: z.string(),
  privateKey: z.string().optional(), // Only stored locally
  userId: z.string().uuid(),
  createdAt: z.date(),
});

export type IdentityKeyPair = z.infer<typeof IdentityKeyPairSchema>;

// Signed Pre-Key
export const SignedPreKeySchema = z.object({
  id: z.number(),
  publicKey: z.string(),
  privateKey: z.string().optional(), // Only stored locally
  signature: z.string(),
  userId: z.string().uuid(),
  createdAt: z.date(),
  expiresAt: z.date(),
});

export type SignedPreKey = z.infer<typeof SignedPreKeySchema>;

// One-Time Pre-Key
export const OneTimePreKeySchema = z.object({
  id: z.number(),
  publicKey: z.string(),
  privateKey: z.string().optional(), // Only stored locally
  userId: z.string().uuid(),
  used: z.boolean().default(false),
  createdAt: z.date(),
});

export type OneTimePreKey = z.infer<typeof OneTimePreKeySchema>;

// Session
export const SessionSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().uuid(),
  peerId: z.string().uuid(),
  rootKey: z.string(),
  sendingChainKey: z.string().optional(),
  receivingChainKey: z.string().optional(),
  sendingMessageNumber: z.number().default(0),
  receivingMessageNumber: z.number().default(0),
  previousSendingChainLength: z.number().default(0),
  dhSendingKeyPair: z.object({
    publicKey: z.string(),
    privateKey: z.string(),
  }).optional(),
  dhReceivingKey: z.string().optional(),
  createdAt: z.date(),
  updatedAt: z.date(),
});

export type Session = z.infer<typeof SessionSchema>;

// Message
export const MessageSchema = z.object({
  id: z.string().uuid(),
  senderId: z.string().uuid(),
  recipientId: z.string().uuid(),
  sessionId: z.string().uuid(),
  ciphertext: z.string(),
  nonce: z.string(),
  authTag: z.string(),
  dhPublicKey: z.string().optional(),
  messageNumber: z.number(),
  previousChainLength: z.number(),
  timestamp: z.date(),
  delivered: z.boolean().default(false),
  read: z.boolean().default(false),
});

export type Message = z.infer<typeof MessageSchema>;

// Message Receipt
export const MessageReceiptSchema = z.object({
  id: z.string().uuid(),
  messageId: z.string().uuid(),
  recipientId: z.string().uuid(),
  status: z.enum(['sent', 'delivered', 'read']),
  timestamp: z.date(),
});

export type MessageReceipt = z.infer<typeof MessageReceiptSchema>;

// Safety Number (for verification)
export const SafetyNumberSchema = z.object({
  userId1: z.string().uuid(),
  userId2: z.string().uuid(),
  number: z.string(),
  qrCode: z.string(),
  verified: z.boolean().default(false),
  verifiedAt: z.date().optional(),
});

export type SafetyNumber = z.infer<typeof SafetyNumberSchema>;

// Authentication Token
export const AuthTokenSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().uuid(),
  deviceId: z.string().uuid(),
  token: z.string(),
  refreshToken: z.string(),
  expiresAt: z.date(),
  createdAt: z.date(),
});

export type AuthToken = z.infer<typeof AuthTokenSchema>;

// Two-Factor Authentication
export const TwoFactorAuthSchema = z.object({
  userId: z.string().uuid(),
  secret: z.string(),
  backupCodes: z.array(z.string()),
  enabled: z.boolean().default(false),
  createdAt: z.date(),
  updatedAt: z.date(),
});

export type TwoFactorAuth = z.infer<typeof TwoFactorAuthSchema>;

// Custom Errors
export class InvalidKeyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'InvalidKeyError';
  }
}

export class SessionNotFoundError extends Error {
  constructor(userId: string, peerId: string) {
    super(`Session not found between user ${userId} and peer ${peerId}`);
    this.name = 'SessionNotFoundError';
  }
}

export class DecryptionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'DecryptionError';
  }
}

export class AuthenticationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'AuthenticationError';
  }
}