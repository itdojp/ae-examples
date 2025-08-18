/**
 * Domain Service: SessionInitiationService
 * 
 * Signal Protocol準拠の鍵交換とセッション開始を管理するドメインサービス
 * X25519鍵交換、Double Ratchet初期化、MITM攻撃検出を実装
 */

import { DomainService } from '../core/DomainService';
import { User } from '../entities/User';
import { SecureSession } from '../entities/SecureSession';
import { SessionId } from '../value-objects/SessionId';
import { UserId } from '../value-objects/UserId';
import { DoubleRatchetState } from '../value-objects/DoubleRatchetState';
import { SafetyNumber } from '../value-objects/SafetyNumber';
import { CryptographicKey } from '../value-objects/CryptographicKey';
import { UserRepository } from '../repositories/UserRepository';
import { SessionRepository } from '../repositories/SessionRepository';
import { CryptographyService } from './CryptographyService';
import { DomainError } from '../core/DomainError';
import { CryptoAlgorithm } from '../enums/CryptoAlgorithm';

export class SessionInitiationService extends DomainService {
  constructor(
    private readonly userRepo: UserRepository,
    private readonly sessionRepo: SessionRepository,
    private readonly cryptoService: CryptographyService
  ) {
    super();
  }

  /**
   * Signal Protocol準拠のセッション開始
   * 
   * X3DH (Extended Triple Diffie-Hellman) 鍵合意プロトコルの実装
   */
  public async initiateSession(
    initiatorId: UserId, 
    recipientId: UserId
  ): Promise<SecureSession> {
    
    // ユーザー存在確認
    const initiator = await this.userRepo.findById(initiatorId);
    const recipient = await this.userRepo.findById(recipientId);
    
    if (!initiator || !recipient) {
      throw new DomainError('One or both users not found');
    }

    // 既存セッション確認
    const existingSession = await this.sessionRepo.findByParticipants(
      initiatorId, 
      recipientId
    );
    
    if (existingSession && existingSession.isActive()) {
      throw new DomainError('Active session already exists between these users');
    }

    try {
      // Signal Protocol X3DH 鍵交換実行
      const sessionData = await this.performX3DHKeyExchange(initiator, recipient);
      
      // Double Ratchet初期化
      const ratchetState = await this.initializeDoubleRatchet(sessionData);
      
      // Safety Number生成
      const safetyNumber = await this.generateSafetyNumber(
        initiator.identityKeyPair.publicKey,
        recipient.identityKeyPair.publicKey,
        initiatorId,
        recipientId
      );

      // セッション作成
      const session = new SecureSession(
        SessionId.generate(),
        [initiatorId, recipientId],
        ratchetState,
        safetyNumber
      );

      // セッション永続化
      await this.sessionRepo.save(session);

      // ドメインイベント発行
      this.publishDomainEvent({
        type: 'SecureSessionInitiated',
        sessionId: session.id.value,
        initiatorId: initiatorId.value,
        recipientId: recipientId.value,
        safetyNumber: safetyNumber.value,
        timestamp: new Date()
      });

      return session;

    } catch (error) {
      throw new DomainError(`Session initiation failed: ${error.message}`);
    }
  }

  /**
   * X3DH (Extended Triple Diffie-Hellman) 鍵交換
   * 
   * Signal Protocol仕様に準拠したセキュア鍵交換
   */
  private async performX3DHKeyExchange(
    initiator: User, 
    recipient: User
  ): Promise<{
    rootKey: CryptographicKey;
    chainKeySend: CryptographicKey;
    chainKeyReceive: CryptographicKey;
  }> {

    // Recipient の事前鍵取得
    const oneTimePreKey = recipient.consumeOneTimePreKey();
    if (!oneTimePreKey) {
      throw new DomainError('No one-time pre-keys available for recipient');
    }

    // Initiator のエフェメラル鍵生成
    const initiatorEphemeral = await this.cryptoService.generateX25519KeyPair();

    try {
      // X3DH 4つのDiffie-Hellman計算
      const dh1 = await this.cryptoService.performECDH(
        initiator.identityKeyPair.privateKey,
        recipient.signedPreKey.publicKey
      );

      const dh2 = await this.cryptoService.performECDH(
        initiatorEphemeral.privateKey,
        recipient.identityKeyPair.publicKey
      );

      const dh3 = await this.cryptoService.performECDH(
        initiatorEphemeral.privateKey,
        recipient.signedPreKey.publicKey
      );

      const dh4 = await this.cryptoService.performECDH(
        initiatorEphemeral.privateKey,
        oneTimePreKey.publicKey
      );

      // 共有秘密の結合（Signal Protocol仕様）
      const sharedSecret = await this.combineSharedSecrets([dh1, dh2, dh3, dh4]);

      // Root Keyとチェーンキー導出
      const keyDerivationResult = await this.deriveInitialKeys(sharedSecret);

      // エフェメラル鍵のセキュアクリーンアップ
      initiatorEphemeral.destroy();
      sharedSecret.destroy();

      return keyDerivationResult;

    } catch (error) {
      // セキュアクリーンアップ
      initiatorEphemeral.destroy();
      throw error;
    }
  }

  /**
   * Double Ratchetアルゴリズム初期化
   */
  private async initializeDoubleRatchet(sessionData: {
    rootKey: CryptographicKey;
    chainKeySend: CryptographicKey;
    chainKeyReceive: CryptographicKey;
  }): Promise<DoubleRatchetState> {

    return DoubleRatchetState.initialize(
      sessionData.rootKey,
      sessionData.chainKeySend,
      sessionData.chainKeyReceive
    );
  }

  /**
   * Safety Number生成（決定的アルゴリズム）
   */
  private async generateSafetyNumber(
    publicKey1: CryptographicKey,
    publicKey2: CryptographicKey,
    userId1: UserId,
    userId2: UserId
  ): Promise<SafetyNumber> {

    // 決定的順序付け（小さいUserIdを先に）
    const [firstKey, secondKey, firstId, secondId] = userId1.value < userId2.value 
      ? [publicKey1, publicKey2, userId1, userId2]
      : [publicKey2, publicKey1, userId2, userId1];

    // Safety Number計算（Signal Protocol準拠）
    const combinedData = new Uint8Array(
      firstKey.getKeyData().length + 
      secondKey.getKeyData().length + 
      firstId.value.length + 
      secondId.value.length
    );

    let offset = 0;
    combinedData.set(firstKey.getKeyData(), offset);
    offset += firstKey.getKeyData().length;
    combinedData.set(secondKey.getKeyData(), offset);
    offset += secondKey.getKeyData().length;
    combinedData.set(new TextEncoder().encode(firstId.value), offset);
    offset += firstId.value.length;
    combinedData.set(new TextEncoder().encode(secondId.value), offset);

    // SHA-256ハッシュ計算
    const hash = await this.cryptoService.hash(combinedData, 'SHA-256');
    
    // 60桁の数値文字列に変換
    const safetyNumberString = this.convertToSafetyNumberString(hash);

    // セキュアクリーンアップ
    combinedData.fill(0);

    return SafetyNumber.fromString(safetyNumberString);
  }

  /**
   * 共有秘密の結合（HKDF使用）
   */
  private async combineSharedSecrets(secrets: CryptographicKey[]): Promise<CryptographicKey> {
    // 全ての共有秘密を結合
    const totalLength = secrets.reduce((sum, secret) => sum + secret.keyLength, 0);
    const combined = new Uint8Array(totalLength);

    let offset = 0;
    for (const secret of secrets) {
      combined.set(secret.getKeyData(), offset);
      offset += secret.keyLength;
    }

    try {
      // HKDF (HMAC-based Key Derivation Function) でキー導出
      const derivedKey = await this.cryptoService.hkdf(
        combined,
        new Uint8Array(0), // salt (empty)
        new TextEncoder().encode('SecureChat-RootKey'), // info
        32 // 256 bits
      );

      return new CryptographicKey(derivedKey, CryptoAlgorithm.AES_256_GCM);

    } finally {
      // セキュアクリーンアップ
      combined.fill(0);
    }
  }

  /**
   * 初期鍵導出（Root Key + Chain Keys）
   */
  private async deriveInitialKeys(sharedSecret: CryptographicKey): Promise<{
    rootKey: CryptographicKey;
    chainKeySend: CryptographicKey;
    chainKeyReceive: CryptographicKey;
  }> {

    // HKDF でマスター鍵材料から3つのキーを導出
    const keyMaterial = await this.cryptoService.hkdf(
      sharedSecret.getKeyData(),
      new Uint8Array(0), // salt
      new TextEncoder().encode('SecureChat-InitialKeys'), // info
      96 // 3 * 32 bytes = 96 bytes
    );

    const rootKey = new CryptographicKey(
      keyMaterial.slice(0, 32),
      CryptoAlgorithm.AES_256_GCM
    );

    const chainKeySend = new CryptographicKey(
      keyMaterial.slice(32, 64),
      CryptoAlgorithm.HMAC_SHA256
    );

    const chainKeyReceive = new CryptographicKey(
      keyMaterial.slice(64, 96),
      CryptoAlgorithm.HMAC_SHA256
    );

    // セキュアクリーンアップ
    keyMaterial.fill(0);

    return { rootKey, chainKeySend, chainKeyReceive };
  }

  /**
   * ハッシュからSafety Number文字列への変換
   */
  private convertToSafetyNumberString(hash: Uint8Array): string {
    // SHA-256ハッシュ(32 bytes)から60桁の数値文字列を生成
    let result = '';
    
    for (let i = 0; i < hash.length && result.length < 60; i++) {
      result += hash[i].toString().padStart(3, '0');
    }

    return result.substring(0, 60);
  }

  /**
   * MITM攻撃検出
   */
  public async detectMITMAttack(
    sessionId: SessionId,
    expectedSafetyNumber: string
  ): Promise<boolean> {
    
    const session = await this.sessionRepo.findById(sessionId);
    if (!session) {
      throw new DomainError('Session not found');
    }

    const actualSafetyNumber = session.safetyNumber.value;
    
    // Safety Number比較（タイミング攻撃耐性）
    const isMITM = !this.constantTimeStringCompare(
      actualSafetyNumber, 
      expectedSafetyNumber
    );

    if (isMITM) {
      this.publishDomainEvent({
        type: 'MITMAttackDetected',
        sessionId: sessionId.value,
        expectedSafetyNumber,
        actualSafetyNumber,
        timestamp: new Date()
      });
    }

    return isMITM;
  }

  /**
   * 定時間文字列比較（タイミング攻撃対策）
   */
  private constantTimeStringCompare(str1: string, str2: string): boolean {
    if (str1.length !== str2.length) {
      return false;
    }

    let result = 0;
    for (let i = 0; i < str1.length; i++) {
      result |= str1.charCodeAt(i) ^ str2.charCodeAt(i);
    }

    return result === 0;
  }
}