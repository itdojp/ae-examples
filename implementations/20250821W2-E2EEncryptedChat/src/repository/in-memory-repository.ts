/**
 * In-Memory Repository Implementation
 * For demo purposes - in production, use a proper database
 */

import { 
  User, 
  Message, 
  ChatSession, 
  KeyBundle 
} from '../domain/entities.js';
import { ChatRepository } from '../services/chat-service.js';

export class InMemoryRepository implements ChatRepository {
  private users: Map<string, User> = new Map();
  private messages: Map<string, Message[]> = new Map();
  private sessions: Map<string, ChatSession> = new Map();
  private keyBundles: Map<string, KeyBundle> = new Map();
  private sessionMessages: Map<string, string[]> = new Map();

  async saveUser(user: User): Promise<void> {
    this.users.set(user.id, user);
  }

  async getUser(userId: string): Promise<User | null> {
    return this.users.get(userId) || null;
  }

  async saveMessage(message: Message): Promise<void> {
    // Find session for this message
    let sessionId: string | null = null;
    for (const [id, session] of this.sessions) {
      if (session.participants.includes(message.senderId) && 
          session.participants.includes(message.recipientId)) {
        sessionId = id;
        break;
      }
    }

    if (sessionId) {
      if (!this.sessionMessages.has(sessionId)) {
        this.sessionMessages.set(sessionId, []);
      }
      this.sessionMessages.get(sessionId)!.push(message.id);
      
      if (!this.messages.has(sessionId)) {
        this.messages.set(sessionId, []);
      }
      this.messages.get(sessionId)!.push(message);
    }
  }

  async getMessages(sessionId: string): Promise<Message[]> {
    return this.messages.get(sessionId) || [];
  }

  async saveSession(session: ChatSession): Promise<void> {
    this.sessions.set(session.id, session);
  }

  async getSession(sessionId: string): Promise<ChatSession | null> {
    return this.sessions.get(sessionId) || null;
  }

  async saveKeyBundle(bundle: KeyBundle): Promise<void> {
    this.keyBundles.set(bundle.userId, bundle);
  }

  async getKeyBundle(userId: string): Promise<KeyBundle | null> {
    return this.keyBundles.get(userId) || null;
  }

  // Additional helper methods
  async getUserByEmail(email: string): Promise<User | null> {
    for (const user of this.users.values()) {
      if (user.email === email) {
        return user;
      }
    }
    return null;
  }

  async getSessionsByUser(userId: string): Promise<ChatSession[]> {
    const sessions: ChatSession[] = [];
    for (const session of this.sessions.values()) {
      if (session.participants.includes(userId)) {
        sessions.push(session);
      }
    }
    return sessions;
  }

  async deleteMessage(messageId: string): Promise<void> {
    for (const messages of this.messages.values()) {
      const index = messages.findIndex(m => m.id === messageId);
      if (index !== -1) {
        messages.splice(index, 1);
        break;
      }
    }
  }

  async updateMessageStatus(
    messageId: string, 
    status: Message['status']
  ): Promise<void> {
    for (const messages of this.messages.values()) {
      const message = messages.find(m => m.id === messageId);
      if (message) {
        message.status = status;
        break;
      }
    }
  }

  // Key management
  async consumeOneTimePreKey(userId: string): Promise<string | null> {
    const bundle = this.keyBundles.get(userId);
    if (!bundle || bundle.oneTimePreKeys.length === 0) {
      return null;
    }
    
    const preKey = bundle.oneTimePreKeys.shift();
    if (preKey) {
      await this.saveKeyBundle(bundle);
      return preKey.key;
    }
    
    return null;
  }

  async getOneTimePreKeyCount(userId: string): Promise<number> {
    const bundle = this.keyBundles.get(userId);
    return bundle ? bundle.oneTimePreKeys.length : 0;
  }

  // Debug methods
  async clear(): Promise<void> {
    this.users.clear();
    this.messages.clear();
    this.sessions.clear();
    this.keyBundles.clear();
    this.sessionMessages.clear();
  }

  async getStats(): Promise<{
    users: number;
    sessions: number;
    messages: number;
    keyBundles: number;
  }> {
    let totalMessages = 0;
    for (const messages of this.messages.values()) {
      totalMessages += messages.length;
    }

    return {
      users: this.users.size,
      sessions: this.sessions.size,
      messages: totalMessages,
      keyBundles: this.keyBundles.size
    };
  }
}