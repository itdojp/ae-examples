/**
 * Domain Entity: SecureSession - セッション集約
 * 
 * Double Ratchet アルゴリズムによるセキュアセッション管理
 * Perfect Forward Secrecy とメッセージの暗号化/復号化を担当
 */

import { DomainEntity } from '../core/DomainEntity';
import { SessionId } from '../value-objects/SessionId';
import { UserId } from '../value-objects/UserId';
import { EncryptedMessage } from '../value-objects/EncryptedMessage';
import { DoubleRatchetState } from '../value-objects/DoubleRatchetState';
import { MessageKey } from '../value-objects/MessageKey';
import { SafetyNumber } from '../value-objects/SafetyNumber';
import { CryptographicKey } from '../value-objects/CryptographicKey';
import { DomainError } from '../core/DomainError';
import { SecurityLevel } from '../enums/SecurityLevel';

export class SecureSession extends DomainEntity<SessionId> {
  private readonly _participants: [UserId, UserId];
  private _ratchetState: DoubleRatchetState;
  private _safetyNumber: SafetyNumber;
  private _isVerified: boolean = false;
  private _verifiedAt?: Date;
  private _createdAt: Date;
  private _lastMessageAt: Date;
  private _messagesExchanged: number = 0;
  private _keyRotationCount: number = 0;

  constructor(
    id: SessionId,
    participants: [UserId, UserId],
    ratchetState: DoubleRatchetState,
    safetyNumber: SafetyNumber
  ) {
    super(id);
    this._participants = participants;
    this._ratchetState = ratchetState;
    this._safetyNumber = safetyNumber;
    this._createdAt = new Date();
    this._lastMessageAt = new Date();

    this.validate();

    this.addDomainEvent({
      type: 'SecureSessionCreated',
      sessionId: this._id.value,
      participants: this._participants.map(p => p.value),
      timestamp: this._createdAt
    });
  }

  /**
   * ビジネスルール: Perfect Forward Secrecy メッセージ暗号化
   */
  public encryptMessage(plaintext: string, messageKey?: MessageKey): EncryptedMessage {
    if (plaintext.length > 10 * 1024 * 1024) { // 10MB limit
      throw new DomainError('Message too large. Maximum size: 10MB');
    }

    // メッセージキーを導出または使用
    const key = messageKey ?? this.deriveMessageKey();
    
    try {
      // AES-256-GCM 暗号化
      const encrypted = EncryptedMessage.create(
        plaintext,
        key,
        this._id,
        this._participants[0] // sender
      );

      // Perfect Forward Secrecy: メッセージキー即座削除
      key.destroy();
      
      this._messagesExchanged++;
      this._lastMessageAt = new Date();

      // 100メッセージごとに自動キーローテーション
      if (this._messagesExchanged % 100 === 0) {
        this.performDHRatchet();
      }

      this.addDomainEvent({
        type: 'MessageEncrypted',
        sessionId: this._id.value,
        messageId: encrypted.messageId,
        messageNumber: this._messagesExchanged,
        timestamp: this._lastMessageAt
      });

      return encrypted;

    } catch (error) {
      key.destroy(); // Ensure cleanup on error
      throw new DomainError(`Encryption failed: ${error.message}`);
    }
  }

  /**
   * ビジネスルール: セキュア復号化と認証確認
   */
  public decryptMessage(encryptedMessage: EncryptedMessage): string {
    if (!this.isParticipant(encryptedMessage.senderId)) {
      throw new DomainError('Invalid sender for this session');
    }

    try {
      const plaintext = encryptedMessage.decrypt(this._ratchetState.currentMessageKey);
      
      this.addDomainEvent({
        type: 'MessageDecrypted',
        sessionId: this._id.value,
        messageId: encryptedMessage.messageId,
        timestamp: new Date()
      });

      return plaintext;

    } catch (error) {
      this.addDomainEvent({
        type: 'MessageDecryptionFailed',
        sessionId: this._id.value,
        messageId: encryptedMessage.messageId,
        error: error.message,
        timestamp: new Date()
      });
      
      throw new DomainError(`Decryption failed: ${error.message}`);
    }
  }

  /**
   * ビジネスルール: Double Ratchet キーローテーション
   */
  public performDHRatchet(): void {
    const oldRootKey = this._ratchetState.rootKey.keyId;
    
    try {
      this._ratchetState = this._ratchetState.performDHRatchet();
      this._keyRotationCount++;

      this.addDomainEvent({
        type: 'DHRatchetPerformed',
        sessionId: this._id.value,
        oldRootKeyId: oldRootKey,
        newRootKeyId: this._ratchetState.rootKey.keyId,
        rotationNumber: this._keyRotationCount,
        timestamp: new Date()
      });

    } catch (error) {
      throw new DomainError(`Key rotation failed: ${error.message}`);
    }
  }

  /**
   * セキュリティルール: エフェメラルメッセージキー導出
   */
  public deriveMessageKey(): MessageKey {
    try {
      const messageKey = this._ratchetState.deriveNextMessageKey();
      
      this.addDomainEvent({
        type: 'MessageKeyDerived',
        sessionId: this._id.value,
        keyId: messageKey.keyId,
        timestamp: new Date()
      });

      return messageKey;

    } catch (error) {
      throw new DomainError(`Message key derivation failed: ${error.message}`);
    }
  }

  /**
   * セキュリティルール: 身元検証管理
   */
  public markAsVerified(): void {
    if (this._isVerified) {
      return; // Already verified
    }

    this._isVerified = true;
    this._verifiedAt = new Date();

    this.addDomainEvent({
      type: 'SessionIdentityVerified',
      sessionId: this._id.value,
      safetyNumber: this._safetyNumber.value,
      timestamp: this._verifiedAt
    });
  }

  public markAsUnverified(): void {
    this._isVerified = false;
    this._verifiedAt = undefined;

    this.addDomainEvent({
      type: 'SessionIdentityCompromised',
      sessionId: this._id.value,
      timestamp: new Date()
    });
  }

  /**
   * ビジネスルール: セッション有効性確認
   */
  public isActive(): boolean {
    const hoursSinceLastMessage = this.hoursSince(this._lastMessageAt);
    return hoursSinceLastMessage < 168; // 7 days
  }

  public isExpired(): boolean {
    return !this.isActive();
  }

  /**
   * セキュリティ評価
   */
  public getSecurityLevel(): SecurityLevel {
    if (!this._isVerified) {
      return SecurityLevel.WARNING;
    }

    if (this._keyRotationCount < 1) {
      return SecurityLevel.MEDIUM;
    }

    return SecurityLevel.HIGH;
  }

  /**
   * ネットワークパケット生成（機密情報除外）
   */
  public createNetworkPacket(encryptedMessage: EncryptedMessage): object {
    return {
      sessionId: this._id.value,
      messageId: encryptedMessage.messageId,
      payload: {
        ciphertext: encryptedMessage.ciphertext,
        nonce: encryptedMessage.nonce,
        authTag: encryptedMessage.authTag
      },
      metadata: {
        algorithm: encryptedMessage.algorithm,
        timestamp: new Date().toISOString()
      }
    };
  }

  /**
   * セキュアクリーンアップ
   */
  public destroy(): void {
    this._ratchetState.destroy();
    this._safetyNumber.destroy();

    this.addDomainEvent({
      type: 'SecureSessionDestroyed',
      sessionId: this._id.value,
      timestamp: new Date()
    });
  }

  // Getters
  public get participants(): [UserId, UserId] {
    return [...this._participants] as [UserId, UserId];
  }

  public get safetyNumber(): SafetyNumber {
    return this._safetyNumber;
  }

  public get isVerified(): boolean {
    return this._isVerified;
  }

  public get verifiedAt(): Date | undefined {
    return this._verifiedAt;
  }

  public get messagesExchanged(): number {
    return this._messagesExchanged;
  }

  public get keyRotationCount(): number {
    return this._keyRotationCount;
  }

  public get currentSessionKey(): CryptographicKey {
    return this._ratchetState.rootKey;
  }

  public get ratchetState(): DoubleRatchetState {
    return this._ratchetState;
  }

  /**
   * セッション参加者確認
   */
  public isParticipant(userId: UserId): boolean {
    return this._participants.some(participant => participant.equals(userId));
  }

  public getOtherParticipant(userId: UserId): UserId {
    if (!this.isParticipant(userId)) {
      throw new DomainError('User is not a participant in this session');
    }

    return this._participants.find(participant => !participant.equals(userId))!;
  }

  /**
   * ドメインルール検証
   */
  protected validate(): void {
    if (!this._participants || this._participants.length !== 2) {
      throw new DomainError('Session must have exactly two participants');
    }

    if (this._participants[0].equals(this._participants[1])) {
      throw new DomainError('Session participants must be different users');
    }

    if (!this._ratchetState) {
      throw new DomainError('Session must have valid ratchet state');
    }

    if (!this._safetyNumber) {
      throw new DomainError('Session must have safety number');
    }
  }

  /**
   * 時間計算ヘルパー
   */
  private hoursSince(date: Date): number {
    const now = new Date();
    const diffTime = Math.abs(now.getTime() - date.getTime());
    return Math.ceil(diffTime / (1000 * 60 * 60));
  }

  /**
   * エンティティ同等性
   */
  public equals(other: SecureSession): boolean {
    return super.equals(other);
  }

  /**
   * デバッグ用文字列表現（機密情報除外）
   */
  public toString(): string {
    return `SecureSession(${this._id.value}, participants: [${this._participants[0].value}, ${this._participants[1].value}], verified: ${this._isVerified}, messages: ${this._messagesExchanged})`;
  }
}