import { Database } from '../db';
import { User } from '../../domain/entities';
import { v4 as uuidv4 } from 'uuid';

export interface UserRepository {
  create(user: Omit<User, 'id' | 'createdAt' | 'updatedAt'>): Promise<User>;
  findById(id: string): Promise<User | null>;
  findByEmail(email: string): Promise<User | null>;
  update(id: string, updates: Partial<User>): Promise<User | null>;
  delete(id: string): Promise<boolean>;
  updateLastSeen(id: string): Promise<void>;
}

export class UserRepositoryImpl implements UserRepository {
  constructor(private db: Database) {}

  async create(user: Omit<User, 'id' | 'createdAt' | 'updatedAt'>): Promise<User> {
    const id = uuidv4();
    const now = new Date();
    
    const query = `
      INSERT INTO users (id, email, display_name, is_verified, created_at, updated_at)
      VALUES ($1, $2, $3, $4, $5, $6)
      RETURNING *
    `;
    
    const result = await this.db.query(query, [
      id,
      user.email,
      user.displayName,
      user.isVerified || false,
      now,
      now
    ]);
    
    return this.mapToEntity(result.rows[0]);
  }

  async findById(id: string): Promise<User | null> {
    const query = 'SELECT * FROM users WHERE id = $1';
    const result = await this.db.query(query, [id]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToEntity(result.rows[0]);
  }

  async findByEmail(email: string): Promise<User | null> {
    const query = 'SELECT * FROM users WHERE email = $1';
    const result = await this.db.query(query, [email]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToEntity(result.rows[0]);
  }

  async update(id: string, updates: Partial<User>): Promise<User | null> {
    const fields: string[] = [];
    const values: any[] = [];
    let paramCount = 1;
    
    if (updates.email !== undefined) {
      fields.push(`email = $${paramCount++}`);
      values.push(updates.email);
    }
    
    if (updates.displayName !== undefined) {
      fields.push(`display_name = $${paramCount++}`);
      values.push(updates.displayName);
    }
    
    if (updates.isVerified !== undefined) {
      fields.push(`is_verified = $${paramCount++}`);
      values.push(updates.isVerified);
    }
    
    if (updates.lastSeen !== undefined) {
      fields.push(`last_seen = $${paramCount++}`);
      values.push(updates.lastSeen);
    }
    
    if (fields.length === 0) {
      return this.findById(id);
    }
    
    values.push(id);
    
    const query = `
      UPDATE users
      SET ${fields.join(', ')}, updated_at = NOW()
      WHERE id = $${paramCount}
      RETURNING *
    `;
    
    const result = await this.db.query(query, values);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToEntity(result.rows[0]);
  }

  async delete(id: string): Promise<boolean> {
    const query = 'DELETE FROM users WHERE id = $1';
    const result = await this.db.query(query, [id]);
    return result.rowCount > 0;
  }

  async updateLastSeen(id: string): Promise<void> {
    const query = 'UPDATE users SET last_seen = NOW() WHERE id = $1';
    await this.db.query(query, [id]);
  }

  private mapToEntity(row: any): User {
    return {
      id: row.id,
      email: row.email,
      displayName: row.display_name,
      isVerified: row.is_verified,
      lastSeen: row.last_seen ? new Date(row.last_seen) : undefined,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at)
    };
  }
}