import { Database } from '../db';
import { Message, MessageReceipt } from '../../domain/entities';
import { v4 as uuidv4 } from 'uuid';

export interface MessageRepository {
  save(message: Message): Promise<Message>;
  findById(id: string): Promise<Message | null>;
  findBySession(sessionId: string, limit?: number, offset?: number): Promise<Message[]>;
  findBetweenUsers(userId1: string, userId2: string, limit?: number, offset?: number): Promise<Message[]>;
  markAsDelivered(messageId: string): Promise<void>;
  markAsRead(messageId: string): Promise<void>;
  delete(messageId: string): Promise<boolean>;
  saveReceipt(receipt: MessageReceipt): Promise<void>;
  getReceipts(messageId: string): Promise<MessageReceipt[]>;
}

export class MessageRepositoryImpl implements MessageRepository {
  constructor(private db: Database) {}

  async save(message: Message): Promise<Message> {
    const query = `
      INSERT INTO messages (
        id, sender_id, recipient_id, session_id, ciphertext, 
        nonce, auth_tag, dh_public_key, message_number, 
        previous_chain_length, delivered, read, timestamp
      )
      VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13)
      RETURNING *
    `;
    
    const result = await this.db.query(query, [
      message.id || uuidv4(),
      message.senderId,
      message.recipientId,
      message.sessionId,
      message.ciphertext,
      message.nonce,
      message.authTag,
      message.dhPublicKey,
      message.messageNumber,
      message.previousChainLength,
      message.delivered,
      message.read,
      message.timestamp
    ]);
    
    return this.mapToMessage(result.rows[0]);
  }

  async findById(id: string): Promise<Message | null> {
    const query = 'SELECT * FROM messages WHERE id = $1';
    const result = await this.db.query(query, [id]);
    
    if (result.rows.length === 0) {
      return null;
    }
    
    return this.mapToMessage(result.rows[0]);
  }

  async findBySession(sessionId: string, limit = 50, offset = 0): Promise<Message[]> {
    const query = `
      SELECT * FROM messages 
      WHERE session_id = $1
      ORDER BY timestamp DESC
      LIMIT $2 OFFSET $3
    `;
    
    const result = await this.db.query(query, [sessionId, limit, offset]);
    return result.rows.map(row => this.mapToMessage(row));
  }

  async findBetweenUsers(userId1: string, userId2: string, limit = 50, offset = 0): Promise<Message[]> {
    const query = `
      SELECT * FROM messages 
      WHERE (sender_id = $1 AND recipient_id = $2) 
         OR (sender_id = $2 AND recipient_id = $1)
      ORDER BY timestamp DESC
      LIMIT $3 OFFSET $4
    `;
    
    const result = await this.db.query(query, [userId1, userId2, limit, offset]);
    return result.rows.map(row => this.mapToMessage(row));
  }

  async markAsDelivered(messageId: string): Promise<void> {
    const query = 'UPDATE messages SET delivered = true WHERE id = $1';
    await this.db.query(query, [messageId]);
  }

  async markAsRead(messageId: string): Promise<void> {
    const query = 'UPDATE messages SET read = true WHERE id = $1';
    await this.db.query(query, [messageId]);
  }

  async delete(messageId: string): Promise<boolean> {
    const query = 'DELETE FROM messages WHERE id = $1';
    const result = await this.db.query(query, [messageId]);
    return result.rowCount > 0;
  }

  async saveReceipt(receipt: MessageReceipt): Promise<void> {
    const query = `
      INSERT INTO message_receipts (id, message_id, recipient_id, status, timestamp)
      VALUES ($1, $2, $3, $4, $5)
      ON CONFLICT (message_id, recipient_id, status) DO UPDATE
      SET timestamp = $5
    `;
    
    await this.db.query(query, [
      receipt.id || uuidv4(),
      receipt.messageId,
      receipt.recipientId,
      receipt.status,
      receipt.timestamp
    ]);
  }

  async getReceipts(messageId: string): Promise<MessageReceipt[]> {
    const query = 'SELECT * FROM message_receipts WHERE message_id = $1 ORDER BY timestamp ASC';
    const result = await this.db.query(query, [messageId]);
    
    return result.rows.map(row => ({
      id: row.id,
      messageId: row.message_id,
      recipientId: row.recipient_id,
      status: row.status,
      timestamp: new Date(row.timestamp)
    }));
  }

  private mapToMessage(row: any): Message {
    return {
      id: row.id,
      senderId: row.sender_id,
      recipientId: row.recipient_id,
      sessionId: row.session_id,
      ciphertext: row.ciphertext,
      nonce: row.nonce,
      authTag: row.auth_tag,
      dhPublicKey: row.dh_public_key,
      messageNumber: row.message_number,
      previousChainLength: row.previous_chain_length,
      delivered: row.delivered,
      read: row.read,
      timestamp: new Date(row.timestamp)
    };
  }
}