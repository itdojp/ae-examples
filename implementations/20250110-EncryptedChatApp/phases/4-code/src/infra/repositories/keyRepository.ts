import { Database } from '../db';
import { 
  IdentityKeyPair, 
  SignedPreKey, 
  OneTimePreKey 
} from '../../domain/entities';
import { v4 as uuidv4 } from 'uuid';

export interface KeyRepository {
  // Identity Keys
  saveIdentityKey(key: IdentityKeyPair): Promise<void>;
  getIdentityKey(userId: string): Promise<IdentityKeyPair | null>;
  
  // Signed Pre-Keys
  saveSignedPreKey(key: SignedPreKey): Promise<void>;
  getSignedPreKey(userId: string): Promise<SignedPreKey | null>;
  getActiveSignedPreKey(userId: string): Promise<SignedPreKey | null>;
  rotateSignedPreKey(userId: string, newKey: SignedPreKey): Promise<void>;
  
  // One-Time Pre-Keys
  saveOneTimePreKeys(keys: OneTimePreKey[]): Promise<void>;
  getOneTimePreKey(userId: string): Promise<OneTimePreKey | null>;
  consumeOneTimePreKey(userId: string, keyId: number): Promise<void>;
  countUnusedOneTimePreKeys(userId: string): Promise<number>;
}

export class KeyRepositoryImpl implements KeyRepository {
  constructor(private db: Database) {}

  async saveIdentityKey(key: IdentityKeyPair): Promise<void> {
    const query = `
      INSERT INTO identity_keys (id, user_id, public_key, created_at)
      VALUES ($1, $2, $3, $4)
      ON CONFLICT (user_id) DO UPDATE
      SET public_key = $3, created_at = $4
    `;
    
    await this.db.query(query, [
      uuidv4(),
      key.userId,
      key.publicKey,
      key.createdAt
    ]);
  }

  async getIdentityKey(userId: string): Promise<IdentityKeyPair | null> {
    const query = 'SELECT * FROM identity_keys WHERE user_id = $1';
    const result = await this.db.query(query, [userId]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    const row = result.rows[0];
    return {
      publicKey: row.public_key,
      userId: row.user_id,
      createdAt: new Date(row.created_at)
    };
  }

  async saveSignedPreKey(key: SignedPreKey): Promise<void> {
    const query = `
      INSERT INTO signed_pre_keys (user_id, key_id, public_key, signature, created_at, expires_at)
      VALUES ($1, $2, $3, $4, $5, $6)
      ON CONFLICT (user_id, key_id) DO UPDATE
      SET public_key = $3, signature = $4, expires_at = $6
    `;
    
    await this.db.query(query, [
      key.userId,
      key.id,
      key.publicKey,
      key.signature,
      key.createdAt,
      key.expiresAt
    ]);
  }

  async getSignedPreKey(userId: string): Promise<SignedPreKey | null> {
    const query = `
      SELECT * FROM signed_pre_keys 
      WHERE user_id = $1 
      ORDER BY created_at DESC 
      LIMIT 1
    `;
    const result = await this.db.query(query, [userId]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToSignedPreKey(result.rows[0]);
  }

  async getActiveSignedPreKey(userId: string): Promise<SignedPreKey | null> {
    const query = `
      SELECT * FROM signed_pre_keys 
      WHERE user_id = $1 AND expires_at > NOW()
      ORDER BY created_at DESC 
      LIMIT 1
    `;
    const result = await this.db.query(query, [userId]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToSignedPreKey(result.rows[0]);
  }

  async rotateSignedPreKey(userId: string, newKey: SignedPreKey): Promise<void> {
    await this.db.transaction(async (client) => {
      // Mark old keys as expired (keep for 5 days for transition)
      await client.query(
        `UPDATE signed_pre_keys 
         SET expires_at = NOW() + INTERVAL '5 days'
         WHERE user_id = $1 AND expires_at > NOW()`,
        [userId]
      );
      
      // Insert new key
      await client.query(
        `INSERT INTO signed_pre_keys (user_id, key_id, public_key, signature, created_at, expires_at)
         VALUES ($1, $2, $3, $4, $5, $6)`,
        [newKey.userId, newKey.id, newKey.publicKey, newKey.signature, newKey.createdAt, newKey.expiresAt]
      );
    });
  }

  async saveOneTimePreKeys(keys: OneTimePreKey[]): Promise<void> {
    if (keys.length === 0) return;
    
    const values: any[] = [];
    const placeholders: string[] = [];
    let paramCount = 1;
    
    for (const key of keys) {
      placeholders.push(`($${paramCount}, $${paramCount + 1}, $${paramCount + 2}, $${paramCount + 3}, $${paramCount + 4})`);
      values.push(key.userId, key.id, key.publicKey, key.used, key.createdAt);
      paramCount += 5;
    }
    
    const query = `
      INSERT INTO one_time_pre_keys (user_id, key_id, public_key, used, created_at)
      VALUES ${placeholders.join(', ')}
      ON CONFLICT (user_id, key_id) DO NOTHING
    `;
    
    await this.db.query(query, values);
  }

  async getOneTimePreKey(userId: string): Promise<OneTimePreKey | null> {
    const query = `
      SELECT * FROM one_time_pre_keys 
      WHERE user_id = $1 AND used = false
      ORDER BY key_id ASC
      LIMIT 1
    `;
    const result = await this.db.query(query, [userId]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToOneTimePreKey(result.rows[0]);
  }

  async consumeOneTimePreKey(userId: string, keyId: number): Promise<void> {
    const query = `
      UPDATE one_time_pre_keys 
      SET used = true 
      WHERE user_id = $1 AND key_id = $2
    `;
    await this.db.query(query, [userId, keyId]);
  }

  async countUnusedOneTimePreKeys(userId: string): Promise<number> {
    const query = `
      SELECT COUNT(*) as count 
      FROM one_time_pre_keys 
      WHERE user_id = $1 AND used = false
    `;
    const result = await this.db.query(query, [userId]);
    return parseInt(result.rows[0].count, 10);
  }

  private mapToSignedPreKey(row: any): SignedPreKey {
    return {
      id: row.key_id,
      publicKey: row.public_key,
      signature: row.signature,
      userId: row.user_id,
      createdAt: new Date(row.created_at),
      expiresAt: new Date(row.expires_at)
    };
  }

  private mapToOneTimePreKey(row: any): OneTimePreKey {
    return {
      id: row.key_id,
      publicKey: row.public_key,
      userId: row.user_id,
      used: row.used,
      createdAt: new Date(row.created_at)
    };
  }
}