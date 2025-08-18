/**
 * Repository Interface: UserRepository
 * 
 * ユーザー集約の永続化を担当するリポジトリインターフェース
 * DDD アーキテクチャパターンに従った抽象化
 */

import { Repository } from '../core/Repository';
import { User } from '../entities/User';
import { UserId } from '../value-objects/UserId';
import { DeviceFingerprint } from '../value-objects/DeviceFingerprint';
import { CryptographicKey } from '../value-objects/CryptographicKey';

export interface UserRepository extends Repository<User, UserId> {
  /**
   * 基本CRUD操作
   */
  findById(id: UserId): Promise<User | null>;
  save(user: User): Promise<void>;
  remove(id: UserId): Promise<void>;
  exists(id: UserId): Promise<boolean>;

  /**
   * ユーザー固有クエリ
   */
  findByEmail(email: string): Promise<User | null>;
  findByPublicKey(publicKey: CryptographicKey): Promise<User | null>;
  findByDeviceFingerprint(fingerprint: DeviceFingerprint): Promise<User[]>;
  
  /**
   * セキュリティクエリ
   */
  findVerifiedUsers(): Promise<User[]>;
  findUsersWithExpiredKeys(): Promise<User[]>;
  findUsersNeedingKeyRotation(): Promise<User[]>;
  findUsersWithLowOneTimePreKeys(): Promise<User[]>;

  /**
   * 検索・フィルタリング
   */
  findUsers(criteria: {
    isVerified?: boolean;
    hasDevices?: boolean;
    createdAfter?: Date;
    lastActiveAfter?: Date;
    keyRotationDue?: boolean;
  }): Promise<User[]>;

  /**
   * 統計・メトリクス
   */
  countTotalUsers(): Promise<number>;
  countVerifiedUsers(): Promise<number>;
  countActiveUsers(since: Date): Promise<number>;

  /**
   * バッチ操作
   */
  saveAll(users: User[]): Promise<void>;
  removeAll(ids: UserId[]): Promise<void>;

  /**
   * セキュリティ運用
   */
  rotateKeysForAllUsers(): Promise<void>;
  cleanupExpiredOneTimePreKeys(): Promise<number>;
  auditSecurityStatus(): Promise<{
    totalUsers: number;
    verifiedUsers: number;
    usersWithExpiredKeys: number;
    usersNeedingRotation: number;
  }>;
}

/**
 * Repository Query Result Types
 */
export interface UserSecurityAudit {
  userId: string;
  isVerified: boolean;
  keyRotationDue: boolean;
  oneTimePreKeysCount: number;
  trustedDevicesCount: number;
  lastKeyRotation: Date;
  securityLevel: 'HIGH' | 'MEDIUM' | 'LOW' | 'WARNING';
}

export interface UserSearchCriteria {
  email?: string;
  isVerified?: boolean;
  hasExpiredKeys?: boolean;
  keyRotationDue?: boolean;
  minOneTimePreKeys?: number;
  createdAfter?: Date;
  createdBefore?: Date;
  lastActiveAfter?: Date;
  lastActiveBefore?: Date;
  trustedDevicesCount?: {
    min?: number;
    max?: number;
  };
}