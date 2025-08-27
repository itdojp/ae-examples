import { User, ChatSession, EncryptedMessage } from '@e2e-chat/shared';

// In-memory database for demo (would use PostgreSQL/MongoDB in production)
interface Database {
  users: Map<string, User & { passwordHash: string; privateKey: string }>;
  sessions: Map<string, ChatSession>;
  messages: Map<string, EncryptedMessage[]>;
  publicKeys: Map<string, string>;
  preKeys: Map<string, string[]>;
}

const db: Database = {
  users: new Map(),
  sessions: new Map(),
  messages: new Map(),
  publicKeys: new Map(),
  preKeys: new Map()
};

export async function initializeDatabase(): Promise<void> {
  console.log('📦 Database initialized (in-memory)');
}

export const userDB = {
  async create(user: User & { passwordHash: string; privateKey: string }): Promise<User> {
    db.users.set(user.id, user);
    db.publicKeys.set(user.id, user.publicKey || '');
    return { ...user, privateKey: undefined, passwordHash: undefined } as any;
  },

  async findByEmail(email: string): Promise<(User & { passwordHash: string; privateKey: string }) | null> {
    const users = Array.from(db.users.values());
    return users.find(u => u.email === email) || null;
  },

  async findById(id: string): Promise<User | null> {
    const user = db.users.get(id);
    if (!user) return null;
    const { passwordHash, privateKey, ...publicUser } = user;
    return publicUser;
  },

  async getAllExcept(excludeId: string): Promise<User[]> {
    const users = Array.from(db.users.values());
    return users
      .filter(u => u.id !== excludeId)
      .map(({ passwordHash, privateKey, ...publicUser }) => publicUser);
  }
};

export const sessionDB = {
  async create(session: ChatSession): Promise<ChatSession> {
    db.sessions.set(session.id, session);
    return session;
  },

  async findById(id: string): Promise<ChatSession | null> {
    return db.sessions.get(id) || null;
  },

  async findByParticipants(userId1: string, userId2: string): Promise<ChatSession | null> {
    const sessions = Array.from(db.sessions.values());
    return sessions.find(s => 
      s.participants.includes(userId1) && s.participants.includes(userId2)
    ) || null;
  },

  async updateVerified(id: string, verified: boolean): Promise<void> {
    const session = db.sessions.get(id);
    if (session) {
      session.verified = verified;
    }
  }
};

export const messageDB = {
  async save(message: EncryptedMessage): Promise<EncryptedMessage> {
    const key = `${message.senderId}-${message.recipientId}`;
    const reverseKey = `${message.recipientId}-${message.senderId}`;
    
    // Save for both sender and recipient views
    if (!db.messages.has(key)) {
      db.messages.set(key, []);
    }
    if (!db.messages.has(reverseKey)) {
      db.messages.set(reverseKey, []);
    }
    
    db.messages.get(key)!.push(message);
    db.messages.get(reverseKey)!.push(message);
    
    return message;
  },

  async getMessages(userId1: string, userId2: string): Promise<EncryptedMessage[]> {
    const key = `${userId1}-${userId2}`;
    return db.messages.get(key) || [];
  }
};

export const keyDB = {
  async savePublicKey(userId: string, publicKey: string): Promise<void> {
    db.publicKeys.set(userId, publicKey);
  },

  async getPublicKey(userId: string): Promise<string | null> {
    return db.publicKeys.get(userId) || null;
  },

  async savePreKeys(userId: string, preKeys: string[]): Promise<void> {
    db.preKeys.set(userId, preKeys);
  },

  async consumePreKey(userId: string): Promise<string | null> {
    const keys = db.preKeys.get(userId);
    if (!keys || keys.length === 0) return null;
    return keys.shift() || null;
  }
};