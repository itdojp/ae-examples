import { User, UserId, Email } from '../entities/User';

export interface UserRepository {
  save(user: User): Promise<void>;
  findById(userId: UserId): Promise<User | null>;
  findByEmail(email: Email): Promise<User | null>;
  update(user: User): Promise<void>;
  delete(userId: UserId): Promise<void>;
  exists(userId: UserId): Promise<boolean>;
}