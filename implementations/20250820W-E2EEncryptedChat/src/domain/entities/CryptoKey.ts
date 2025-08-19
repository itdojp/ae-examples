export interface IdentityKey {
  publicKey: Uint8Array;
  privateKey: Uint8Array;
}

export interface SignedPreKey {
  id: number;
  publicKey: Uint8Array;
  privateKey: Uint8Array;
  signature: Uint8Array;
  timestamp: Date;
}

export interface OneTimePreKey {
  id: number;
  publicKey: Uint8Array;
  privateKey: Uint8Array;
}

export interface DeviceKey {
  id: string;
  publicKey: Uint8Array;
  privateKey: Uint8Array;
}

export interface EphemeralKey {
  publicKey: Uint8Array;
  privateKey?: Uint8Array;
}

export interface CryptoKeyBundle {
  identityKey: IdentityKey;
  signedPreKey: SignedPreKey;
  oneTimePreKeys: OneTimePreKey[];
  deviceKey: DeviceKey;
}

export interface PreKeyBundle {
  identityKey: Uint8Array;
  signedPreKey: {
    id: number;
    publicKey: Uint8Array;
    signature: Uint8Array;
  };
  oneTimePreKey?: {
    id: number;
    publicKey: Uint8Array;
  };
}