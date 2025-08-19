export type UserId = string;
export type Email = string;

export enum TrustLevel {
  UNVERIFIED = 'unverified',
  VERIFIED = 'verified',
  TRUSTED = 'trusted'
}

export interface Device {
  id: string;
  name: string;
  fingerprint: string;
  createdAt: Date;
  lastSeenAt: Date;
}

export interface User {
  id: UserId;
  email: Email;
  displayName: string;
  createdAt: Date;
  devices: Device[];
  trustLevel: TrustLevel;
}