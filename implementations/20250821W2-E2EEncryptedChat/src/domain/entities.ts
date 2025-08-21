/**
 * Domain Entities for E2E Encrypted Chat
 */

import { z } from 'zod';

// User Entity
export const UserSchema = z.object({
  id: z.string().uuid(),
  email: z.string().email(),
  displayName: z.string().min(1).max(100),
  createdAt: z.date(),
  devices: z.array(z.object({
    id: z.string(),
    name: z.string(),
    addedAt: z.date(),
    lastSeen: z.date().optional()
  })),
  trustLevel: z.enum(['unverified', 'verified', 'trusted']),
  publicKey: z.string()
});

export type User = z.infer<typeof UserSchema>;

// Message Entity
export const MessageSchema = z.object({
  id: z.string().uuid(),
  senderId: z.string().uuid(),
  recipientId: z.string().uuid(),
  ciphertext: z.string(),
  nonce: z.string(),
  timestamp: z.date(),
  ephemeralKey: z.string().optional(),
  messageType: z.enum(['text', 'image', 'file', 'typing']),
  status: z.enum(['sending', 'sent', 'delivered', 'read', 'failed'])
});

export type Message = z.infer<typeof MessageSchema>;

// Chat Session Entity
export const ChatSessionSchema = z.object({
  id: z.string().uuid(),
  participants: z.array(z.string().uuid()).min(2).max(2),
  createdAt: z.date(),
  lastActivity: z.date(),
  verified: z.boolean(),
  securityNumber: z.string().optional(),
  ratchetState: z.any() // Complex state object
});

export type ChatSession = z.infer<typeof ChatSessionSchema>;

// Key Bundle Entity
export const KeyBundleSchema = z.object({
  userId: z.string().uuid(),
  identityKey: z.string(),
  signedPreKey: z.object({
    id: z.number(),
    key: z.string(),
    signature: z.string()
  }),
  oneTimePreKeys: z.array(z.object({
    id: z.number(),
    key: z.string()
  }))
});

export type KeyBundle = z.infer<typeof KeyBundleSchema>;

// Security Event Entity
export const SecurityEventSchema = z.object({
  id: z.string().uuid(),
  type: z.enum([
    'key_change',
    'verification_completed',
    'verification_failed',
    'suspicious_activity',
    'device_added',
    'device_removed'
  ]),
  userId: z.string().uuid(),
  details: z.record(z.any()),
  timestamp: z.date(),
  severity: z.enum(['info', 'warning', 'critical'])
});

export type SecurityEvent = z.infer<typeof SecurityEventSchema>;

// Value Objects
export class SecurityNumber {
  constructor(
    private readonly localFingerprint: string,
    private readonly remoteFingerprint: string
  ) {}

  verify(other: SecurityNumber): boolean {
    return this.localFingerprint === other.remoteFingerprint &&
           this.remoteFingerprint === other.localFingerprint;
  }

  toDisplayString(): string {
    return `${this.localFingerprint}\n${this.remoteFingerprint}`;
  }

  toQRCode(): string {
    return JSON.stringify({
      version: 1,
      local: this.localFingerprint,
      remote: this.remoteFingerprint
    });
  }
}

export class MessageContent {
  constructor(
    private readonly text: string,
    private readonly mentions?: string[],
    private readonly attachments?: string[]
  ) {
    if (text.length > 10000) {
      throw new Error('Message too long');
    }
  }

  getText(): string {
    return this.text;
  }

  getMentions(): string[] {
    return this.mentions || [];
  }

  getAttachments(): string[] {
    return this.attachments || [];
  }
}