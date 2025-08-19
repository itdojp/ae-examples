import { vi } from 'vitest';

global.crypto = {
  getRandomValues: (array: Uint8Array) => {
    for (let i = 0; i < array.length; i++) {
      array[i] = Math.floor(Math.random() * 256);
    }
    return array;
  },
} as any;

vi.mock('libsodium-wrappers', () => ({
  ready: Promise.resolve(),
  crypto_sign_keypair: () => ({
    publicKey: new Uint8Array(32),
    privateKey: new Uint8Array(64)
  }),
  crypto_box_keypair: () => ({
    publicKey: new Uint8Array(32),
    privateKey: new Uint8Array(32)
  }),
  crypto_sign_detached: () => new Uint8Array(64),
  crypto_sign_verify_detached: () => true,
  crypto_box_easy: () => new Uint8Array(48),
  crypto_box_open_easy: () => new Uint8Array(32),
  crypto_secretbox_easy: () => new Uint8Array(48),
  crypto_secretbox_open_easy: () => new Uint8Array(32),
  crypto_scalarmult: () => new Uint8Array(32),
  crypto_auth: () => new Uint8Array(32),
  crypto_auth_verify: () => true,
  crypto_generichash: () => new Uint8Array(32),
  crypto_box_NONCEBYTES: 24,
  crypto_secretbox_NONCEBYTES: 24,
  randombytes_buf: (length: number) => new Uint8Array(length),
  to_base64: (data: Uint8Array) => Buffer.from(data).toString('base64'),
  from_string: (str: string) => new TextEncoder().encode(str),
  to_string: (data: Uint8Array) => new TextDecoder().decode(data)
}));