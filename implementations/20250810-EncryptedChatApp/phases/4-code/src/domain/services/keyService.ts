import { 
  IdentityKeyPair,
  SignedPreKey,
  OneTimePreKey
} from '../entities';
import { KeyManager } from '../crypto/keyManager';
import { KeyRepository } from '../../infra/repositories/keyRepository';
import { Database } from '../../infra/db';

export interface KeyService {
  generateUserKeys(userId: string): Promise<{
    identityKey: IdentityKeyPair;
    signedPreKey: SignedPreKey;
    oneTimePreKeys: OneTimePreKey[];
  }>;
  rotateSignedPreKey(userId: string): Promise<SignedPreKey>;
  generateOneTimePreKeys(userId: string, count: number): Promise<OneTimePreKey[]>;
  getPublicKeyBundle(userId: string): Promise<{
    identityKey: string;
    signedPreKey: { id: number; key: string; signature: string };
    oneTimePreKey?: { id: number; key: string };
  }>;
  consumeOneTimePreKey(userId: string, keyId: number): Promise<void>;
}

export class KeyServiceImpl implements KeyService {
  private keyManager: KeyManager;
  private keyRepository: KeyRepository;
  
  constructor(
    private db: Database,
    keyRepository: KeyRepository
  ) {
    this.keyRepository = keyRepository;
  }

  async initialize() {
    this.keyManager = await KeyManager.getInstance();
  }

  async generateUserKeys(userId: string) {
    if (!this.keyManager) {
      await this.initialize();
    }

    // Generate identity key pair
    const identityKey = this.keyManager.generateIdentityKeyPair(userId);
    
    // Generate signed pre-key
    const signedPreKey = this.keyManager.generateSignedPreKey(
      userId,
      identityKey.privateKey!,
      1
    );
    
    // Generate one-time pre-keys
    const oneTimePreKeys = this.keyManager.generateOneTimePreKeys(userId, 1, 100);
    
    // Save keys to database
    await this.db.transaction(async (client) => {
      // Save identity key
      await client.query(
        `INSERT INTO identity_keys (user_id, public_key, created_at)
         VALUES ($1, $2, NOW())
         ON CONFLICT (user_id) DO UPDATE SET public_key = $2`,
        [userId, identityKey.publicKey]
      );
      
      // Save signed pre-key
      await client.query(
        `INSERT INTO signed_pre_keys (user_id, key_id, public_key, signature, created_at, expires_at)
         VALUES ($1, $2, $3, $4, $5, $6)`,
        [userId, signedPreKey.id, signedPreKey.publicKey, signedPreKey.signature, 
         signedPreKey.createdAt, signedPreKey.expiresAt]
      );
      
      // Save one-time pre-keys
      for (const otpk of oneTimePreKeys) {
        await client.query(
          `INSERT INTO one_time_pre_keys (user_id, key_id, public_key, used, created_at)
           VALUES ($1, $2, $3, false, $4)`,
          [userId, otpk.id, otpk.publicKey, otpk.createdAt]
        );
      }
    });
    
    return {
      identityKey,
      signedPreKey,
      oneTimePreKeys
    };
  }

  async rotateSignedPreKey(userId: string): Promise<SignedPreKey> {
    if (!this.keyManager) {
      await this.initialize();
    }

    // Get identity key from database
    const identityKey = await this.keyRepository.getIdentityKey(userId);
    if (!identityKey) {
      throw new Error('Identity key not found');
    }
    
    // Get current signed pre-key to determine next ID
    const currentKey = await this.keyRepository.getSignedPreKey(userId);
    const nextKeyId = currentKey ? currentKey.id + 1 : 1;
    
    // Generate new signed pre-key
    // Note: We need the private identity key which should be stored securely
    // In production, this would be retrieved from secure storage
    const newSignedPreKey = this.keyManager.generateSignedPreKey(
      userId,
      '', // Private key would be retrieved from secure storage
      nextKeyId
    );
    
    // Rotate in database
    await this.keyRepository.rotateSignedPreKey(userId, newSignedPreKey);
    
    return newSignedPreKey;
  }

  async generateOneTimePreKeys(userId: string, count: number): Promise<OneTimePreKey[]> {
    if (!this.keyManager) {
      await this.initialize();
    }

    // Get last key ID from database
    const query = `
      SELECT MAX(key_id) as max_id 
      FROM one_time_pre_keys 
      WHERE user_id = $1
    `;
    const result = await this.db.query(query, [userId]);
    const lastKeyId = result.rows[0].max_id || 0;
    const startId = lastKeyId + 1;
    
    // Generate new keys
    const newKeys = this.keyManager.generateOneTimePreKeys(userId, startId, count);
    
    // Save to database
    await this.keyRepository.saveOneTimePreKeys(newKeys);
    
    return newKeys;
  }

  async getPublicKeyBundle(userId: string) {
    // Get identity key
    const identityKey = await this.keyRepository.getIdentityKey(userId);
    if (!identityKey) {
      throw new Error('User keys not found');
    }
    
    // Get active signed pre-key
    const signedPreKey = await this.keyRepository.getActiveSignedPreKey(userId);
    if (!signedPreKey) {
      throw new Error('No active signed pre-key');
    }
    
    // Get one available one-time pre-key
    const oneTimePreKey = await this.keyRepository.getOneTimePreKey(userId);
    
    return {
      identityKey: identityKey.publicKey,
      signedPreKey: {
        id: signedPreKey.id,
        key: signedPreKey.publicKey,
        signature: signedPreKey.signature
      },
      oneTimePreKey: oneTimePreKey ? {
        id: oneTimePreKey.id,
        key: oneTimePreKey.publicKey
      } : undefined
    };
  }

  async consumeOneTimePreKey(userId: string, keyId: number): Promise<void> {
    await this.keyRepository.consumeOneTimePreKey(userId, keyId);
    
    // Check if we need to replenish
    const unusedCount = await this.keyRepository.countUnusedOneTimePreKeys(userId);
    if (unusedCount < 10) {
      // Generate more keys
      await this.generateOneTimePreKeys(userId, 90);
    }
  }
}