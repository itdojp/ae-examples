import { Database } from '../db';
import { Session } from '../../domain/entities';
import { v4 as uuidv4 } from 'uuid';

export interface SessionRepository {
  create(session: Session): Promise<Session>;
  findById(id: string): Promise<Session | null>;
  findByUsers(userId: string, peerId: string): Promise<Session | null>;
  update(session: Session): Promise<Session>;
  delete(id: string): Promise<boolean>;
  saveSkippedMessageKey(sessionId: string, dhPublicKey: string, messageNumber: number, messageKey: string): Promise<void>;
  getSkippedMessageKey(sessionId: string, dhPublicKey: string, messageNumber: number): Promise<string | null>;
  deleteSkippedMessageKey(sessionId: string, dhPublicKey: string, messageNumber: number): Promise<void>;
}

export class SessionRepositoryImpl implements SessionRepository {
  constructor(private db: Database) {}

  async create(session: Session): Promise<Session> {
    const query = `
      INSERT INTO sessions (
        id, user_id, peer_id, root_key, sending_chain_key, receiving_chain_key,
        sending_message_number, receiving_message_number, previous_sending_chain_length,
        dh_sending_public_key, dh_sending_private_key, dh_receiving_key,
        created_at, updated_at
      )
      VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14)
      RETURNING *
    `;
    
    const result = await this.db.query(query, [
      session.id || uuidv4(),
      session.userId,
      session.peerId,
      session.rootKey,
      session.sendingChainKey,
      session.receivingChainKey,
      session.sendingMessageNumber,
      session.receivingMessageNumber,
      session.previousSendingChainLength,
      session.dhSendingKeyPair?.publicKey,
      session.dhSendingKeyPair?.privateKey,
      session.dhReceivingKey,
      session.createdAt,
      session.updatedAt
    ]);
    
    return this.mapToSession(result.rows[0]);
  }

  async findById(id: string): Promise<Session | null> {
    const query = 'SELECT * FROM sessions WHERE id = $1';
    const result = await this.db.query(query, [id]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToSession(result.rows[0]);
  }

  async findByUsers(userId: string, peerId: string): Promise<Session | null> {
    const query = 'SELECT * FROM sessions WHERE user_id = $1 AND peer_id = $2';
    const result = await this.db.query(query, [userId, peerId]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToSession(result.rows[0]);
  }

  async update(session: Session): Promise<Session> {
    const query = `
      UPDATE sessions SET
        root_key = $2,
        sending_chain_key = $3,
        receiving_chain_key = $4,
        sending_message_number = $5,
        receiving_message_number = $6,
        previous_sending_chain_length = $7,
        dh_sending_public_key = $8,
        dh_sending_private_key = $9,
        dh_receiving_key = $10,
        updated_at = NOW()
      WHERE id = $1
      RETURNING *
    `;
    
    const result = await this.db.query(query, [
      session.id,
      session.rootKey,
      session.sendingChainKey,
      session.receivingChainKey,
      session.sendingMessageNumber,
      session.receivingMessageNumber,
      session.previousSendingChainLength,
      session.dhSendingKeyPair?.publicKey,
      session.dhSendingKeyPair?.privateKey,
      session.dhReceivingKey
    ]);
    
    if (result.rows.length === 0) {
      throw new Error(`Session ${session.id} not found`);
    }
    
    return this.mapToSession(result.rows[0]);
  }

  async delete(id: string): Promise<boolean> {
    const query = 'DELETE FROM sessions WHERE id = $1';
    const result = await this.db.query(query, [id]);
    return result.rowCount > 0;
  }

  async saveSkippedMessageKey(
    sessionId: string, 
    dhPublicKey: string, 
    messageNumber: number, 
    messageKey: string
  ): Promise<void> {
    const query = `
      INSERT INTO skipped_message_keys (id, session_id, dh_public_key, message_number, message_key, created_at)
      VALUES ($1, $2, $3, $4, $5, NOW())
      ON CONFLICT (session_id, dh_public_key, message_number) DO UPDATE
      SET message_key = $5
    `;
    
    await this.db.query(query, [
      uuidv4(),
      sessionId,
      dhPublicKey,
      messageNumber,
      messageKey
    ]);
  }

  async getSkippedMessageKey(
    sessionId: string, 
    dhPublicKey: string, 
    messageNumber: number
  ): Promise<string | null> {
    const query = `
      SELECT message_key FROM skipped_message_keys 
      WHERE session_id = $1 AND dh_public_key = $2 AND message_number = $3
    `;
    
    const result = await this.db.query(query, [sessionId, dhPublicKey, messageNumber]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return result.rows[0].message_key;
  }

  async deleteSkippedMessageKey(
    sessionId: string, 
    dhPublicKey: string, 
    messageNumber: number
  ): Promise<void> {
    const query = `
      DELETE FROM skipped_message_keys 
      WHERE session_id = $1 AND dh_public_key = $2 AND message_number = $3
    `;
    
    await this.db.query(query, [sessionId, dhPublicKey, messageNumber]);
  }

  private mapToSession(row: any): Session {
    return {
      id: row.id,
      userId: row.user_id,
      peerId: row.peer_id,
      rootKey: row.root_key,
      sendingChainKey: row.sending_chain_key,
      receivingChainKey: row.receiving_chain_key,
      sendingMessageNumber: row.sending_message_number,
      receivingMessageNumber: row.receiving_message_number,
      previousSendingChainLength: row.previous_sending_chain_length,
      dhSendingKeyPair: row.dh_sending_public_key ? {
        publicKey: row.dh_sending_public_key,
        privateKey: row.dh_sending_private_key
      } : undefined,
      dhReceivingKey: row.dh_receiving_key,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at)
    };
  }
}