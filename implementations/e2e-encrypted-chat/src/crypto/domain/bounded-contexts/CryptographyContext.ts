/**
 * Bounded Context: Cryptography
 * 
 * 暗号化操作、鍵管理、アルゴリズム実装を統合的に管理する境界コンテキスト
 * Signal Protocol、Perfect Forward Secrecy、タイミング攻撃対策を含む
 */

import { BoundedContext } from '../core/BoundedContext';
import { CryptographyService } from '../services/CryptographyService';
import { CryptographicKey } from '../value-objects/CryptographicKey';
import { CryptoAlgorithm } from '../enums/CryptoAlgorithm';
import { DomainError } from '../core/DomainError';

export class CryptographyContext extends BoundedContext {
  private readonly cryptoService: CryptographyService;
  private readonly supportedAlgorithms: Set<CryptoAlgorithm>;
  private readonly keyCache: Map<string, CryptographicKey>;
  private readonly performanceMetrics: Map<string, number[]>;

  constructor(cryptoService: CryptographyService) {
    super('Cryptography');
    this.cryptoService = cryptoService;
    this.supportedAlgorithms = new Set([
      CryptoAlgorithm.AES_256_GCM,
      CryptoAlgorithm.X25519,
      CryptoAlgorithm.Ed25519,
      CryptoAlgorithm.ChaCha20_Poly1305,
      CryptoAlgorithm.HMAC_SHA256
    ]);
    this.keyCache = new Map();
    this.performanceMetrics = new Map();
  }

  /**
   * コンテキスト境界内での暗号化操作
   */
  public async encrypt(
    plaintext: string | Uint8Array,
    key: CryptographicKey,
    algorithm?: CryptoAlgorithm
  ): Promise<{
    ciphertext: Uint8Array;
    nonce: Uint8Array;
    authTag: Uint8Array;
  }> {
    this.validateContextBoundary();
    
    const startTime = performance.now();
    
    try {
      const result = await this.cryptoService.encrypt(
        plaintext,
        key,
        algorithm ?? key.algorithm
      );

      this.recordPerformanceMetric('encryption', performance.now() - startTime);
      return result;

    } catch (error) {
      this.handleCryptographicError('Encryption failed', error);
      throw error;
    }
  }

  /**
   * コンテキスト境界内での復号化操作
   */
  public async decrypt(
    encryptedData: {
      ciphertext: Uint8Array;
      nonce: Uint8Array;
      authTag: Uint8Array;
    },
    key: CryptographicKey
  ): Promise<Uint8Array> {
    this.validateContextBoundary();
    
    const startTime = performance.now();
    
    try {
      const result = await this.cryptoService.decrypt(encryptedData, key);
      
      this.recordPerformanceMetric('decryption', performance.now() - startTime);
      return result;

    } catch (error) {
      this.handleCryptographicError('Decryption failed', error);
      throw error;
    }
  }

  /**
   * セキュア鍵生成
   */
  public async generateKey(
    algorithm: CryptoAlgorithm,
    options?: {
      keyId?: string;
      maxUsageCount?: number;
      cacheKey?: boolean;
    }
  ): Promise<CryptographicKey> {
    this.validateAlgorithmSupport(algorithm);
    
    const startTime = performance.now();
    
    try {
      const keyPair = await this.cryptoService.generateKeyPair(algorithm);
      const key = new CryptographicKey(
        keyPair.privateKey,
        algorithm,
        options?.keyId,
        options?.maxUsageCount
      );

      // オプショナルキーキャッシュ
      if (options?.cacheKey && options.keyId) {
        this.keyCache.set(options.keyId, key);
        
        // 自動クリーンアップ設定（5分後）
        setTimeout(() => {
          const cachedKey = this.keyCache.get(options.keyId!);
          if (cachedKey) {
            cachedKey.destroy();
            this.keyCache.delete(options.keyId!);
          }
        }, 5 * 60 * 1000);
      }

      this.recordPerformanceMetric('keyGeneration', performance.now() - startTime);
      
      this.publishDomainEvent({
        type: 'CryptographicKeyGenerated',
        context: this.name,
        algorithm,
        keyId: key.keyId,
        timestamp: new Date()
      });

      return key;

    } catch (error) {
      this.handleCryptographicError('Key generation failed', error);
      throw error;
    }
  }

  /**
   * HKDF (HMAC-based Key Derivation Function)
   */
  public async deriveKey(
    inputKeyMaterial: Uint8Array,
    salt: Uint8Array,
    info: Uint8Array,
    outputLength: number
  ): Promise<CryptographicKey> {
    this.validateContextBoundary();
    
    const startTime = performance.now();
    
    try {
      const derivedKeyData = await this.cryptoService.hkdf(
        inputKeyMaterial,
        salt,
        info,
        outputLength
      );

      const key = new CryptographicKey(
        derivedKeyData,
        CryptoAlgorithm.AES_256_GCM // Default algorithm for derived keys
      );

      this.recordPerformanceMetric('keyDerivation', performance.now() - startTime);
      return key;

    } catch (error) {
      this.handleCryptographicError('Key derivation failed', error);
      throw error;
    }
  }

  /**
   * デジタル署名生成
   */
  public async sign(
    data: Uint8Array,
    privateKey: CryptographicKey
  ): Promise<Uint8Array> {
    this.validateContextBoundary();
    
    if (privateKey.algorithm !== CryptoAlgorithm.Ed25519) {
      throw new DomainError('Invalid key algorithm for signing. Ed25519 required.');
    }

    const startTime = performance.now();
    
    try {
      const signature = await this.cryptoService.sign(data, privateKey);
      
      this.recordPerformanceMetric('signing', performance.now() - startTime);
      return signature;

    } catch (error) {
      this.handleCryptographicError('Signing failed', error);
      throw error;
    }
  }

  /**
   * デジタル署名検証
   */
  public async verify(
    data: Uint8Array,
    signature: Uint8Array,
    publicKey: CryptographicKey
  ): Promise<boolean> {
    this.validateContextBoundary();
    
    if (publicKey.algorithm !== CryptoAlgorithm.Ed25519) {
      throw new DomainError('Invalid key algorithm for verification. Ed25519 required.');
    }

    const startTime = performance.now();
    
    try {
      const isValid = await this.cryptoService.verify(data, signature, publicKey);
      
      this.recordPerformanceMetric('verification', performance.now() - startTime);
      
      this.publishDomainEvent({
        type: 'DigitalSignatureVerified',
        context: this.name,
        isValid,
        publicKeyId: publicKey.keyId,
        timestamp: new Date()
      });

      return isValid;

    } catch (error) {
      this.handleCryptographicError('Signature verification failed', error);
      throw error;
    }
  }

  /**
   * ハッシュ計算
   */
  public async hash(
    data: Uint8Array,
    algorithm: 'SHA-256' | 'SHA-512' = 'SHA-256'
  ): Promise<Uint8Array> {
    this.validateContextBoundary();
    
    const startTime = performance.now();
    
    try {
      const hash = await this.cryptoService.hash(data, algorithm);
      
      this.recordPerformanceMetric('hashing', performance.now() - startTime);
      return hash;

    } catch (error) {
      this.handleCryptographicError('Hashing failed', error);
      throw error;
    }
  }

  /**
   * コンテキスト境界の健全性チェック
   */
  public async performHealthCheck(): Promise<{
    status: 'healthy' | 'degraded' | 'critical';
    metrics: object;
    issues: string[];
  }> {
    const issues: string[] = [];
    let status: 'healthy' | 'degraded' | 'critical' = 'healthy';

    try {
      // 基本暗号化操作テスト
      const testKey = await this.generateKey(CryptoAlgorithm.AES_256_GCM);
      const testData = new TextEncoder().encode('health-check-test');
      
      const encrypted = await this.encrypt(testData, testKey);
      const decrypted = await this.decrypt(encrypted, testKey);
      
      if (!this.arraysEqual(testData, decrypted)) {
        issues.push('Cryptographic round-trip test failed');
        status = 'critical';
      }

      testKey.destroy();

    } catch (error) {
      issues.push(`Health check failed: ${error.message}`);
      status = 'critical';
    }

    // パフォーマンスメトリクスチェック
    const avgEncryptionTime = this.getAverageMetric('encryption');
    if (avgEncryptionTime > 50) { // 50ms threshold
      issues.push(`Encryption performance degraded: ${avgEncryptionTime}ms`);
      status = status === 'critical' ? 'critical' : 'degraded';
    }

    // キーキャッシュサイズチェック
    if (this.keyCache.size > 1000) {
      issues.push('Key cache size exceeded recommended limit');
      status = status === 'critical' ? 'critical' : 'degraded';
    }

    return {
      status,
      metrics: this.getPerformanceMetrics(),
      issues
    };
  }

  /**
   * コンテキスト境界のセキュアクリーンアップ
   */
  public async cleanup(): Promise<void> {
    // キャッシュされたキーの安全な破棄
    for (const [keyId, key] of this.keyCache.entries()) {
      key.destroy();
    }
    this.keyCache.clear();

    // パフォーマンスメトリクスクリア
    this.performanceMetrics.clear();

    this.publishDomainEvent({
      type: 'CryptographyContextCleanedUp',
      context: this.name,
      timestamp: new Date()
    });
  }

  /**
   * アルゴリズムサポート検証
   */
  private validateAlgorithmSupport(algorithm: CryptoAlgorithm): void {
    if (!this.supportedAlgorithms.has(algorithm)) {
      throw new DomainError(`Unsupported algorithm: ${algorithm}`);
    }
  }

  /**
   * コンテキスト境界検証
   */
  private validateContextBoundary(): void {
    if (!this.isContextActive()) {
      throw new DomainError('Cryptography context is not active');
    }
  }

  /**
   * 暗号化エラーハンドリング
   */
  private handleCryptographicError(message: string, error: any): void {
    this.publishDomainEvent({
      type: 'CryptographicError',
      context: this.name,
      error: message,
      details: error.message,
      timestamp: new Date()
    });
  }

  /**
   * パフォーマンスメトリクス記録
   */
  private recordPerformanceMetric(operation: string, duration: number): void {
    if (!this.performanceMetrics.has(operation)) {
      this.performanceMetrics.set(operation, []);
    }
    
    const metrics = this.performanceMetrics.get(operation)!;
    metrics.push(duration);
    
    // 直近100件のみ保持
    if (metrics.length > 100) {
      metrics.shift();
    }
  }

  /**
   * 平均メトリクス取得
   */
  private getAverageMetric(operation: string): number {
    const metrics = this.performanceMetrics.get(operation);
    if (!metrics || metrics.length === 0) {
      return 0;
    }
    
    return metrics.reduce((sum, val) => sum + val, 0) / metrics.length;
  }

  /**
   * パフォーマンスメトリクス取得
   */
  private getPerformanceMetrics(): object {
    const result: any = {};
    
    for (const [operation, metrics] of this.performanceMetrics.entries()) {
      if (metrics.length > 0) {
        result[operation] = {
          average: this.getAverageMetric(operation),
          samples: metrics.length,
          min: Math.min(...metrics),
          max: Math.max(...metrics)
        };
      }
    }
    
    return result;
  }

  /**
   * 配列同等性チェック
   */
  private arraysEqual(a: Uint8Array, b: Uint8Array): boolean {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }

  // サポートアルゴリズム取得
  public getSupportedAlgorithms(): CryptoAlgorithm[] {
    return Array.from(this.supportedAlgorithms);
  }

  // キャッシュ統計
  public getCacheStatistics(): {
    size: number;
    keyIds: string[];
  } {
    return {
      size: this.keyCache.size,
      keyIds: Array.from(this.keyCache.keys())
    };
  }
}