import { UserId } from '../entities/User';
import { CryptoKeyBundle, OneTimePreKey, PreKeyBundle } from '../entities/CryptoKey';

export interface KeyRepository {
  saveKeyBundle(userId: UserId, bundle: CryptoKeyBundle): Promise<void>;
  getKeyBundle(userId: UserId): Promise<CryptoKeyBundle | null>;
  consumeOneTimePreKey(userId: UserId): Promise<OneTimePreKey | null>;
  getPreKeyBundle(userId: UserId): Promise<PreKeyBundle | null>;
  updateSignedPreKey(userId: UserId, bundle: CryptoKeyBundle): Promise<void>;
  addOneTimePreKeys(userId: UserId, keys: OneTimePreKey[]): Promise<void>;
  getOneTimePreKeyCount(userId: UserId): Promise<number>;
}