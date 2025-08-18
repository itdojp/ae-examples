/**
 * Domain Entity: User - ユーザー集約ルート
 * 
 * ユーザーの身元、暗号化キー、デバイス管理を担当するドメインエンティティ
 * Perfect Forward Secrecyと鍵ローテーションを実装
 */

import { DomainEntity } from '../core/DomainEntity';
import { UserId } from '../value-objects/UserId';
import { IdentityKeyPair } from '../value-objects/IdentityKeyPair';
import { SignedPreKey } from '../value-objects/SignedPreKey';
import { OneTimePreKey } from '../value-objects/OneTimePreKey';
import { DeviceFingerprint } from '../value-objects/DeviceFingerprint';
import { DomainError } from '../core/DomainError';
import { CryptographicKey } from '../value-objects/CryptographicKey';

export class User extends DomainEntity<UserId> {
  private readonly _identityKeyPair: IdentityKeyPair;
  private _signedPreKey: SignedPreKey;
  private _oneTimePreKeys: OneTimePreKey[];
  private _trustedDevices: DeviceFingerprint[];
  private _isVerified: boolean = false;
  private _createdAt: Date;
  private _lastKeyRotation: Date;

  constructor(
    id: UserId,
    identityKeyPair: IdentityKeyPair,
    signedPreKey: SignedPreKey,
    oneTimePreKeys: OneTimePreKey[] = []
  ) {
    super(id);
    this._identityKeyPair = identityKeyPair;
    this._signedPreKey = signedPreKey;
    this._oneTimePreKeys = [...oneTimePreKeys];
    this._trustedDevices = [];
    this._createdAt = new Date();
    this._lastKeyRotation = new Date();

    this.validate();
  }

  /**
   * ビジネスルール: 署名済み事前鍵は7日で更新が必要
   */
  public rotateSignedPreKey(): SignedPreKey {
    const daysSinceRotation = this.daysSince(this._lastKeyRotation);
    
    if (daysSinceRotation < 7) {
      throw new DomainError(
        `Signed pre-key rotation not due. Last rotation: ${daysSinceRotation} days ago. Required: 7 days.`
      );
    }

    const newSignedPreKey = SignedPreKey.generate(this._identityKeyPair);
    this._signedPreKey = newSignedPreKey;
    this._lastKeyRotation = new Date();

    this.addDomainEvent({
      type: 'SignedPreKeyRotated',
      userId: this._id.value,
      keyId: newSignedPreKey.keyId,
      timestamp: this._lastKeyRotation
    });

    return newSignedPreKey;
  }

  /**
   * ビジネスルール: 一度限り事前鍵は使用後即座に削除
   */
  public consumeOneTimePreKey(): OneTimePreKey | null {
    const oneTimeKey = this._oneTimePreKeys.shift();
    
    if (!oneTimeKey) {
      this.addDomainEvent({
        type: 'OneTimePreKeysExhausted',
        userId: this._id.value,
        timestamp: new Date()
      });
      return null;
    }

    this.addDomainEvent({
      type: 'OneTimePreKeyConsumed',
      userId: this._id.value,
      keyId: oneTimeKey.keyId,
      timestamp: new Date()
    });

    return oneTimeKey;
  }

  /**
   * ビジネスルール: 新しいデバイスは検証が必要
   */
  public addTrustedDevice(deviceFingerprint: DeviceFingerprint): void {
    const existingDevice = this._trustedDevices.find(
      device => device.equals(deviceFingerprint)
    );

    if (existingDevice) {
      throw new DomainError('Device already trusted');
    }

    this._trustedDevices.push(deviceFingerprint);

    this.addDomainEvent({
      type: 'TrustedDeviceAdded',
      userId: this._id.value,
      deviceFingerprint: deviceFingerprint.value,
      timestamp: new Date()
    });
  }

  /**
   * セキュリティルール: デバイス信頼性確認
   */
  public isDeviceTrusted(deviceFingerprint: DeviceFingerprint): boolean {
    return this._trustedDevices.some(device => device.equals(deviceFingerprint));
  }

  /**
   * ビジネスルール: 一度限り事前鍵の補充（最低10個維持）
   */
  public replenishOneTimePreKeys(newKeys: OneTimePreKey[]): void {
    if (this._oneTimePreKeys.length + newKeys.length > 100) {
      throw new DomainError('Too many one-time pre-keys. Maximum: 100');
    }

    this._oneTimePreKeys.push(...newKeys);

    this.addDomainEvent({
      type: 'OneTimePreKeysReplenished',
      userId: this._id.value,
      keyCount: newKeys.length,
      totalKeys: this._oneTimePreKeys.length,
      timestamp: new Date()
    });
  }

  /**
   * セキュリティルール: 身元検証状態の管理
   */
  public markAsVerified(): void {
    if (this._isVerified) {
      return; // Already verified
    }

    this._isVerified = true;

    this.addDomainEvent({
      type: 'UserIdentityVerified',
      userId: this._id.value,
      timestamp: new Date()
    });
  }

  public markAsUnverified(): void {
    if (!this._isVerified) {
      return; // Already unverified
    }

    this._isVerified = false;

    this.addDomainEvent({
      type: 'UserIdentityCompromised',
      userId: this._id.value,
      timestamp: new Date()
    });
  }

  /**
   * セキュアクリーンアップ: メモリ内の暗号化マテリアルを安全に削除
   */
  public destroy(): void {
    this._identityKeyPair.destroy();
    this._signedPreKey.destroy();
    this._oneTimePreKeys.forEach(key => key.destroy());
    this._oneTimePreKeys = [];

    this.addDomainEvent({
      type: 'UserSecurelyDestroyed',
      userId: this._id.value,
      timestamp: new Date()
    });
  }

  // Getters
  public get identityKeyPair(): IdentityKeyPair {
    return this._identityKeyPair;
  }

  public get signedPreKey(): SignedPreKey {
    return this._signedPreKey;
  }

  public get oneTimePreKeysCount(): number {
    return this._oneTimePreKeys.length;
  }

  public get isVerified(): boolean {
    return this._isVerified;
  }

  public get trustedDevicesCount(): number {
    return this._trustedDevices.length;
  }

  public get needsKeyRotation(): boolean {
    return this.daysSince(this._lastKeyRotation) >= 7;
  }

  public get needsOneTimePreKeyReplenishment(): boolean {
    return this._oneTimePreKeys.length < 10;
  }

  /**
   * ドメインルール検証
   */
  protected validate(): void {
    if (!this._identityKeyPair) {
      throw new DomainError('User must have identity key pair');
    }

    if (!this._signedPreKey) {
      throw new DomainError('User must have signed pre-key');
    }

    if (this._oneTimePreKeys.length > 100) {
      throw new DomainError('Too many one-time pre-keys');
    }

    if (this._trustedDevices.length > 50) {
      throw new DomainError('Too many trusted devices');
    }
  }

  /**
   * 日数計算ヘルパー
   */
  private daysSince(date: Date): number {
    const now = new Date();
    const diffTime = Math.abs(now.getTime() - date.getTime());
    return Math.ceil(diffTime / (1000 * 60 * 60 * 24));
  }

  /**
   * エンティティ同等性
   */
  public equals(other: User): boolean {
    return super.equals(other);
  }

  /**
   * デバッグ用文字列表現（機密情報除外）
   */
  public toString(): string {
    return `User(${this._id.value}, verified: ${this._isVerified}, devices: ${this._trustedDevices.length}, oneTimeKeys: ${this._oneTimePreKeys.length})`;
  }
}