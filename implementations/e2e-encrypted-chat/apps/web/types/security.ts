export interface EncryptionStatus {
  isEncrypted: boolean;
  algorithm: 'AES-256' | 'ChaCha20-Poly1305';
  keyId: string;
  lastRotated: Date;
  verified: boolean;
}

export interface SafetyNumber {
  localNumber: string;
  remoteNumber: string;
  verified: boolean;
  lastVerified?: Date;
}

export interface SecureMessage {
  id: string;
  content: string;
  timestamp: Date;
  senderId: string;
  receiverId: string;
  encryptionStatus: EncryptionStatus;
  delivered: boolean;
  read: boolean;
}

export interface DeviceInfo {
  id: string;
  name: string;
  platform: string;
  lastSeen: Date;
  verified: boolean;
  fingerprint: string;
}

export interface ChatSession {
  id: string;
  participants: string[];
  encryptionStatus: EncryptionStatus;
  safetyNumbers: Record<string, SafetyNumber>;
  lastActivity: Date;
  isActive: boolean;
}

export interface SecurityMetrics {
  encryptionLatency: number;
  keyRotationDue: boolean;
  verificationStatus: 'verified' | 'unverified' | 'compromised';
  lastSecurityCheck: Date;
}