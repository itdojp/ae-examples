import { UserId } from './User';

export type SessionId = string;
export type MessageKey = Uint8Array;

export interface DoubleRatchetState {
  rootKey: Uint8Array;
  sendingChainKey: Uint8Array;
  receivingChainKey: Uint8Array;
  sendingChainLength: number;
  receivingChainLength: number;
  previousSendingChainLength: number;
  remotePublicKey: Uint8Array;
  localPublicKey: Uint8Array;
  localPrivateKey: Uint8Array;
}

export interface ChatSession {
  id: SessionId;
  participants: UserId[];
  ratchetState: DoubleRatchetState;
  messageKeys: MessageKey[];
  verified: boolean;
  createdAt: Date;
  lastActivityAt: Date;
}