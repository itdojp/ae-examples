import { ChatAggregate } from '../aggregates/ChatAggregate';
import { SessionId } from '../entities/Session';
import { UserId } from '../entities/User';

export interface ChatRepository {
  save(chat: ChatAggregate): Promise<void>;
  findById(chatId: SessionId): Promise<ChatAggregate | null>;
  findByParticipants(userIds: UserId[]): Promise<ChatAggregate[]>;
  delete(chatId: SessionId): Promise<void>;
}