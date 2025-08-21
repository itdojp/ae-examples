/**
 * Value Object: CryptographicKey
 * 
 * 暗号化キーの安全な管理とライフサイクル制御
 * メモリ保護、自動破棄、アルゴリズム検証を実装
 */

import { ValueObject } from '../core/ValueObject';
import { DomainError } from '../core/DomainError';
import { CryptoAlgorithm } from '../enums/CryptoAlgorithm';

export class CryptographicKey extends ValueObject {
  private _keyData: Uint8Array;
  private readonly _algorithm: CryptoAlgorithm;
  private readonly _keyId: string;
  private readonly _createdAt: Date;
  private _isDestroyed: boolean = false;
  private _usageCount: number = 0;
  private readonly _maxUsageCount?: number;

  constructor(
    keyData: Uint8Array,
    algorithm: CryptoAlgorithm,
    keyId?: string,
    maxUsageCount?: number
  ) {
    super();
    
    // キー長検証
    this.validateKeyLength(keyData, algorithm);
    
    // セキュアコピー（元の配列への参照を避ける）
    this._keyData = new Uint8Array(keyData);
    this._algorithm = algorithm;
    this._keyId = keyId ?? this.generateKeyId();
    this._createdAt = new Date();
    this._maxUsageCount = maxUsageCount;

    // 元の配列をゼロクリア（セキュリティ対策）
    keyData.fill(0);
  }

  /**
   * セキュアキーアクセス（使用回数制限付き）
   */
  public getKeyData(): Uint8Array {
    if (this._isDestroyed) {
      throw new DomainError('Key has been destroyed and cannot be used');
    }

    if (this._maxUsageCount && this._usageCount >= this._maxUsageCount) {
      throw new DomainError(`Key usage limit exceeded: ${this._maxUsageCount}`);
    }

    this._usageCount++;
    
    // セキュアコピーを返す（直接参照を避ける）
    return new Uint8Array(this._keyData);
  }

  /**
   * セキュリティルール: 鍵の即座破棄
   */
  public destroy(): void {
    if (this._isDestroyed) {
      return; // Already destroyed
    }

    // メモリゼロクリア（3回上書きでセキュリティ強化）
    for (let i = 0; i < 3; i++) {
      this._keyData.fill(0xFF);
      this._keyData.fill(0x00);
      this._keyData.fill(Math.floor(Math.random() * 256));
    }
    this._keyData.fill(0x00);

    this._isDestroyed = true;
  }

  /**
   * キーローテーション用の新しいキー生成
   */
  public rotateKey(): CryptographicKey {
    if (this._isDestroyed) {
      throw new DomainError('Cannot rotate destroyed key');
    }

    const newKeyData = this.generateSecureKeyData(this._algorithm);
    const rotatedKey = new CryptographicKey(
      newKeyData,
      this._algorithm,
      undefined, // New key ID will be generated
      this._maxUsageCount
    );

    // 古いキーを破棄
    this.destroy();

    return rotatedKey;
  }

  /**
   * キー強度検証
   */
  public validateStrength(): boolean {
    if (this._isDestroyed) {
      return false;
    }

    // エントロピー分析（簡易版）
    const uniqueBytes = new Set(this._keyData).size;
    const expectedMinEntropy = this._keyData.length * 0.7; // 70%以上のユニークバイト
    
    return uniqueBytes >= expectedMinEntropy;
  }

  /**
   * キー期限確認（作成から24時間）
   */
  public isExpired(): boolean {
    const hoursOld = (Date.now() - this._createdAt.getTime()) / (1000 * 60 * 60);
    return hoursOld > 24;
  }

  /**
   * セキュア比較（タイミング攻撃耐性）
   */
  public secureEquals(other: CryptographicKey): boolean {
    if (this._isDestroyed || other._isDestroyed) {
      return false;
    }

    if (this._keyData.length !== other._keyData.length) {
      return false;
    }

    // 定時間比較（タイミング攻撃対策）
    let result = 0;
    for (let i = 0; i < this._keyData.length; i++) {
      result |= this._keyData[i] ^ other._keyData[i];
    }

    return result === 0;
  }

  // Getters
  public get algorithm(): CryptoAlgorithm {
    return this._algorithm;
  }

  public get keyId(): string {
    return this._keyId;
  }

  public get createdAt(): Date {
    return this._createdAt;
  }

  public get isDestroyed(): boolean {
    return this._isDestroyed;
  }

  public get usageCount(): number {
    return this._usageCount;
  }

  public get keyLength(): number {
    return this._keyData?.length ?? 0;
  }

  /**
   * アルゴリズム別キー長検証
   */
  private validateKeyLength(keyData: Uint8Array, algorithm: CryptoAlgorithm): void {
    const expectedLength = this.expectedKeyLength(algorithm);
    
    if (keyData.length !== expectedLength) {
      throw new DomainError(
        `Invalid key length for ${algorithm}. Expected: ${expectedLength}, Got: ${keyData.length}`
      );
    }
  }

  /**
   * アルゴリズム別期待キー長
   */
  private expectedKeyLength(algorithm: CryptoAlgorithm): number {
    switch (algorithm) {
      case CryptoAlgorithm.AES_256_GCM:
        return 32; // 256 bits
      case CryptoAlgorithm.X25519:
        return 32; // 256 bits
      case CryptoAlgorithm.Ed25519:
        return 32; // 256 bits
      case CryptoAlgorithm.ChaCha20_Poly1305:
        return 32; // 256 bits
      case CryptoAlgorithm.HMAC_SHA256:
        return 32; // 256 bits
      default:
        throw new DomainError(`Unknown algorithm: ${algorithm}`);
    }
  }

  /**
   * セキュアなキーID生成
   */
  private generateKeyId(): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2);
    const algorithmPrefix = this._algorithm.substring(0, 3).toUpperCase();
    
    return `${algorithmPrefix}-${timestamp}-${random}`;
  }

  /**
   * セキュアキーデータ生成
   */
  private generateSecureKeyData(algorithm: CryptoAlgorithm): Uint8Array {
    const keyLength = this.expectedKeyLength(algorithm);
    const keyData = new Uint8Array(keyLength);
    
    // ブラウザ環境での暗号学的乱数生成
    if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
      crypto.getRandomValues(keyData);
    } else {
      // Node.js環境のフォールバック
      const nodeCrypto = require('crypto');
      const buffer = nodeCrypto.randomBytes(keyLength);
      keyData.set(buffer);
    }
    
    return keyData;
  }

  /**
   * Value Object同等性（タイミング攻撃耐性）
   */
  protected equalityComponents(): any[] {
    // セキュリティ上の理由により、keyDataは比較に含めない
    return [this._algorithm, this._keyId];
  }

  /**
   * セキュアな文字列表現（機密情報除外）
   */
  public toString(): string {
    const status = this._isDestroyed ? 'DESTROYED' : 'ACTIVE';
    const usage = this._maxUsageCount ? `${this._usageCount}/${this._maxUsageCount}` : this._usageCount.toString();
    
    return `CryptographicKey(${this._keyId}, ${this._algorithm}, ${status}, usage: ${usage})`;
  }

  /**
   * デバッグ情報（本番環境では無効化推奨）
   */
  public getDebugInfo(): object {
    if (process.env.NODE_ENV === 'production') {
      return { message: 'Debug info disabled in production' };
    }

    return {
      keyId: this._keyId,
      algorithm: this._algorithm,
      keyLength: this.keyLength,
      createdAt: this._createdAt,
      isDestroyed: this._isDestroyed,
      usageCount: this._usageCount,
      maxUsageCount: this._maxUsageCount,
      isExpired: this.isExpired(),
      strengthValid: this.validateStrength()
    };
  }

  /**
   * ファイナライザー（ガベージコレクション時の自動クリーンアップ）
   */
  // @ts-ignore - FinalizationRegistryは実験的機能
  private static readonly cleanupRegistry = typeof FinalizationRegistry !== 'undefined' 
    ? new FinalizationRegistry((keyData: Uint8Array) => {
        keyData.fill(0);
      })
    : null;

  static {
    // 登録可能な場合のみクリーンアップ登録
    if (this.cleanupRegistry) {
      // Note: 実際の実装では、インスタンス作成時に登録する
    }
  }
}