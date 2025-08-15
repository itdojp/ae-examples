import { z } from 'zod';

// ============================================
// Authentication Contracts
// ============================================

export const RegisterUserRequest = z.object({
  email: z.string().email('Invalid email format'),
  password: z.string()
    .min(12, 'Password must be at least 12 characters')
    .regex(
      /^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]/,
      'Password must contain uppercase, lowercase, number, and special character'
    ),
  displayName: z.string().min(1).max(100),
});

export const LoginRequest = z.object({
  email: z.string().email(),
  password: z.string(),
  deviceFingerprint: z.string().min(1),
  totpCode: z.string().regex(/^\d{6}$/).optional(),
});

export const RefreshTokenRequest = z.object({
  refreshToken: z.string().min(1),
});

export const Enable2FARequest = z.object({
  userId: z.string().uuid(),
});

export const Verify2FARequest = z.object({
  userId: z.string().uuid(),
  code: z.string().regex(/^\d{6}$/),
});

// ============================================
// Key Management Contracts
// ============================================

export const KeyBundle = z.object({
  identityKey: z.string(),
  signedPreKey: z.object({
    id: z.number(),
    key: z.string(),
    signature: z.string(),
  }),
  oneTimePreKey: z.object({
    id: z.number(),
    key: z.string(),
  }).optional(),
});

export const UploadKeysRequest = z.object({
  identityKey: z.string(),
  signedPreKey: z.object({
    id: z.number(),
    key: z.string(),
    signature: z.string(),
  }),
  oneTimePreKeys: z.array(z.object({
    id: z.number(),
    key: z.string(),
  })),
});

export const RotateSignedPreKeyRequest = z.object({
  signedPreKey: z.object({
    id: z.number(),
    key: z.string(),
    signature: z.string(),
  }),
});

// ============================================
// Messaging Contracts
// ============================================

export const SendMessageRequest = z.object({
  recipientId: z.string().uuid(),
  ciphertext: z.string(),
  nonce: z.string(),
  authTag: z.string(),
  dhPublicKey: z.string().optional(),
  messageNumber: z.number().int().nonnegative(),
  previousChainLength: z.number().int().nonnegative(),
});

export const GetMessagesRequest = z.object({
  userId: z.string().uuid(),
  limit: z.number().int().min(1).max(100).default(50),
  offset: z.number().int().nonnegative().default(0),
});

export const MessageReceiptRequest = z.object({
  status: z.enum(['delivered', 'read']),
});

// ============================================
// Session Contracts
// ============================================

export const EstablishSessionRequest = z.object({
  ephemeralPublicKey: z.string(),
});

export const SessionResponse = z.object({
  id: z.string().uuid(),
  userId: z.string().uuid(),
  peerId: z.string().uuid(),
  established: z.boolean(),
  createdAt: z.string().datetime(),
});

// ============================================
// Verification Contracts
// ============================================

export const SafetyNumberResponse = z.object({
  safetyNumber: z.string(),
  qrCode: z.string(),
});

// ============================================
// Response Contracts
// ============================================

export const UserResponse = z.object({
  id: z.string().uuid(),
  email: z.string().email(),
  displayName: z.string(),
  isVerified: z.boolean(),
  createdAt: z.string().datetime(),
  lastSeen: z.string().datetime().optional(),
});

export const AuthTokenResponse = z.object({
  token: z.string(),
  refreshToken: z.string(),
  expiresIn: z.number(),
  tokenType: z.literal('Bearer'),
});

export const MessageResponse = z.object({
  id: z.string().uuid(),
  senderId: z.string().uuid(),
  recipientId: z.string().uuid(),
  ciphertext: z.string(),
  nonce: z.string(),
  authTag: z.string(),
  timestamp: z.string().datetime(),
  delivered: z.boolean(),
  read: z.boolean(),
});

export const MessagesListResponse = z.object({
  messages: z.array(MessageResponse),
  total: z.number(),
  hasMore: z.boolean(),
});

export const TwoFactorSetupResponse = z.object({
  secret: z.string(),
  qrCode: z.string(),
  backupCodes: z.array(z.string()),
});

// ============================================
// Error Contracts
// ============================================

export const ErrorResponse = z.object({
  error: z.string(),
  message: z.string(),
  details: z.record(z.any()).optional(),
});

// ============================================
// WebSocket Contracts
// ============================================

export const WebSocketMessage = z.discriminatedUnion('type', [
  z.object({
    type: z.literal('message'),
    payload: MessageResponse,
  }),
  z.object({
    type: z.literal('receipt'),
    payload: z.object({
      messageId: z.string().uuid(),
      status: z.enum(['delivered', 'read']),
      timestamp: z.string().datetime(),
    }),
  }),
  z.object({
    type: z.literal('typing'),
    payload: z.object({
      userId: z.string().uuid(),
      isTyping: z.boolean(),
    }),
  }),
  z.object({
    type: z.literal('presence'),
    payload: z.object({
      userId: z.string().uuid(),
      status: z.enum(['online', 'offline', 'away']),
      lastSeen: z.string().datetime().optional(),
    }),
  }),
  z.object({
    type: z.literal('keyRotation'),
    payload: z.object({
      userId: z.string().uuid(),
      keyType: z.enum(['signedPreKey', 'identityKey']),
    }),
  }),
]);

// ============================================
// Type Exports
// ============================================

export type RegisterUserRequest = z.infer<typeof RegisterUserRequest>;
export type LoginRequest = z.infer<typeof LoginRequest>;
export type RefreshTokenRequest = z.infer<typeof RefreshTokenRequest>;
export type Enable2FARequest = z.infer<typeof Enable2FARequest>;
export type Verify2FARequest = z.infer<typeof Verify2FARequest>;

export type KeyBundle = z.infer<typeof KeyBundle>;
export type UploadKeysRequest = z.infer<typeof UploadKeysRequest>;
export type RotateSignedPreKeyRequest = z.infer<typeof RotateSignedPreKeyRequest>;

export type SendMessageRequest = z.infer<typeof SendMessageRequest>;
export type GetMessagesRequest = z.infer<typeof GetMessagesRequest>;
export type MessageReceiptRequest = z.infer<typeof MessageReceiptRequest>;

export type EstablishSessionRequest = z.infer<typeof EstablishSessionRequest>;
export type SessionResponse = z.infer<typeof SessionResponse>;

export type SafetyNumberResponse = z.infer<typeof SafetyNumberResponse>;

export type UserResponse = z.infer<typeof UserResponse>;
export type AuthTokenResponse = z.infer<typeof AuthTokenResponse>;
export type MessageResponse = z.infer<typeof MessageResponse>;
export type MessagesListResponse = z.infer<typeof MessagesListResponse>;
export type TwoFactorSetupResponse = z.infer<typeof TwoFactorSetupResponse>;

export type ErrorResponse = z.infer<typeof ErrorResponse>;
export type WebSocketMessage = z.infer<typeof WebSocketMessage>;