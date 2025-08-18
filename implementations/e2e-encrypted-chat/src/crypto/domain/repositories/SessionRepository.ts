/**
 * Repository Interface: SessionRepository
 * 
 * セキュアセッション集約の永続化を担当するリポジトリインターフェース  
 * Perfect Forward Secrecy と鍵ローテーション履歴の管理を含む
 */

import { Repository } from '../core/Repository';
import { SecureSession } from '../entities/SecureSession';
import { SessionId } from '../value-objects/SessionId';
import { UserId } from '../value-objects/UserId';
import { SafetyNumber } from '../value-objects/SafetyNumber';

export interface SessionRepository extends Repository<SecureSession, SessionId> {
  /**
   * 基本CRUD操作
   */
  findById(id: SessionId): Promise<SecureSession | null>;
  save(session: SecureSession): Promise<void>;
  remove(id: SessionId): Promise<void>;
  exists(id: SessionId): Promise<boolean>;

  /**
   * セッション固有クエリ
   */
  findByParticipants(user1: UserId, user2: UserId): Promise<SecureSession | null>;
  findActiveSessionsByUser(userId: UserId): Promise<SecureSession[]>;
  findSessionsBySafetyNumber(safetyNumber: SafetyNumber): Promise<SecureSession[]>;

  /**
   * セキュリティクエリ
   */
  findVerifiedSessions(): Promise<SecureSession[]>;
  findUnverifiedSessions(): Promise<SecureSession[]>;
  findExpiredSessions(): Promise<SecureSession[]>;
  findSessionsNeedingKeyRotation(): Promise<SecureSession[]>;
  findHighActivitySessions(messageThreshold: number): Promise<SecureSession[]>;

  /**
   * セッション検索・フィルタリング
   */
  findSessions(criteria: SessionSearchCriteria): Promise<SecureSession[]>;

  /**
   * セッション統計
   */
  countActiveSessions(): Promise<number>;
  countVerifiedSessions(): Promise<number>;
  countSessionsByUser(userId: UserId): Promise<number>;
  getSessionMetrics(): Promise<SessionMetrics>;

  /**
   * セッション履歴・監査
   */
  getSessionHistory(sessionId: SessionId): Promise<SessionHistoryEntry[]>;
  getKeyRotationHistory(sessionId: SessionId): Promise<KeyRotationEntry[]>;
  getMessageStatistics(sessionId: SessionId): Promise<MessageStatistics>;

  /**
   * バッチ操作・メンテナンス
   */
  cleanupExpiredSessions(): Promise<number>;
  rotateKeysForAllSessions(): Promise<void>;
  removeSessionsOlderThan(date: Date): Promise<number>;

  /**
   * セキュリティ運用
   */
  auditSessionSecurity(): Promise<SessionSecurityAudit[]>;
  detectAnomalousActivity(): Promise<SecurityAnomaly[]>;
  generateSecurityReport(timeRange: {
    start: Date;
    end: Date;
  }): Promise<SessionSecurityReport>;

  /**
   * パフォーマンス最適化
   */
  getSessionsWithHighMessageVolume(threshold: number): Promise<SecureSession[]>;
  findSessionsForArchival(inactiveDays: number): Promise<SecureSession[]>;
  optimizeSessionStorage(): Promise<{
    sessionsArchived: number;
    spaceReclaimed: number;
  }>;
}

/**
 * Repository Query Types
 */
export interface SessionSearchCriteria {
  participantId?: UserId;
  isVerified?: boolean;
  isActive?: boolean;
  createdAfter?: Date;
  createdBefore?: Date;
  lastMessageAfter?: Date;
  lastMessageBefore?: Date;
  minMessagesExchanged?: number;
  maxMessagesExchanged?: number;
  keyRotationCount?: {
    min?: number;
    max?: number;
  };
  securityLevel?: 'HIGH' | 'MEDIUM' | 'LOW' | 'WARNING';
}

export interface SessionMetrics {
  totalSessions: number;
  activeSessions: number;
  verifiedSessions: number;
  averageMessagesPerSession: number;
  averageSessionDuration: number; // in hours
  keyRotationsToday: number;
  securityAnomalies: number;
}

export interface SessionHistoryEntry {
  timestamp: Date;
  event: 'CREATED' | 'VERIFIED' | 'KEY_ROTATED' | 'MESSAGE_SENT' | 'EXPIRED' | 'TERMINATED';
  details: {
    [key: string]: any;
  };
}

export interface KeyRotationEntry {
  timestamp: Date;
  rotationType: 'AUTOMATIC' | 'MANUAL' | 'SECURITY_INCIDENT';
  oldKeyId: string;
  newKeyId: string;
  messagesSinceLastRotation: number;
}

export interface MessageStatistics {
  totalMessages: number;
  messagesLast24h: number;
  messagesLast7d: number;
  averageMessageSize: number;
  peakActivity: {
    timestamp: Date;
    messagesPerHour: number;
  };
}

export interface SessionSecurityAudit {
  sessionId: string;
  participants: [string, string];
  isVerified: boolean;
  securityLevel: 'HIGH' | 'MEDIUM' | 'LOW' | 'WARNING';
  keyRotationStatus: 'CURRENT' | 'DUE' | 'OVERDUE';
  messagesExchanged: number;
  lastActivity: Date;
  riskFactors: string[];
  recommendations: string[];
}

export interface SecurityAnomaly {
  sessionId: string;
  type: 'HIGH_MESSAGE_VOLUME' | 'UNUSUAL_TIMING' | 'KEY_REUSE' | 'FAILED_ROTATIONS' | 'MITM_SUSPECTED';
  severity: 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL';
  detectedAt: Date;
  details: {
    [key: string]: any;
  };
  automaticMitigation?: string;
  requiresInvestigation: boolean;
}

export interface SessionSecurityReport {
  timeRange: {
    start: Date;
    end: Date;
  };
  summary: {
    totalSessions: number;
    newSessions: number;
    terminatedSessions: number;
    keyRotations: number;
    securityIncidents: number;
  };
  metrics: SessionMetrics;
  anomalies: SecurityAnomaly[];
  recommendations: string[];
  complianceStatus: {
    pfsCompliance: number; // percentage
    encryptionCompliance: number; // percentage
    keyRotationCompliance: number; // percentage
    overallScore: number; // percentage
  };
}