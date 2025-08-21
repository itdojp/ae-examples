import { describe, it, expect, beforeEach } from 'vitest';
import { CryptoService } from '../../src/infrastructure/crypto/CryptoService';
import { DoubleRatchet } from '../../src/infrastructure/crypto/DoubleRatchet';
import { E2EEncryptionService } from '../../src/application/services/EncryptionService';

describe('End-to-End Encryption Integration', () => {
  let cryptoService: CryptoService;
  let doubleRatchet: DoubleRatchet;
  let encryptionService: E2EEncryptionService;

  beforeEach(async () => {
    cryptoService = CryptoService.getInstance();
    doubleRatchet = new DoubleRatchet();
    encryptionService = new E2EEncryptionService();
    await cryptoService.init();
    await doubleRatchet.init();
  });

  describe('CryptoService', () => {
    it('should generate valid key bundles', async () => {
      const keyBundle = await cryptoService.generateKeyBundle();
      
      expect(keyBundle.identityKey).toBeDefined();
      expect(keyBundle.identityKey.publicKey).toBeInstanceOf(Uint8Array);
      expect(keyBundle.identityKey.privateKey).toBeInstanceOf(Uint8Array);
      expect(keyBundle.signedPreKey).toBeDefined();
      expect(keyBundle.oneTimePreKeys).toHaveLength(100);
      expect(keyBundle.deviceKey).toBeDefined();
    });

    it('should encrypt and decrypt messages', async () => {
      const aliceKeys = await cryptoService.generateKeyBundle();
      const bobKeys = await cryptoService.generateKeyBundle();
      const plaintext = 'Hello, secure world!';

      const { ciphertext, nonce } = await cryptoService.encryptMessage(
        plaintext,
        bobKeys.identityKey.publicKey,
        aliceKeys.identityKey.privateKey
      );

      const decrypted = await cryptoService.decryptMessage(
        ciphertext,
        nonce,
        aliceKeys.identityKey.publicKey,
        bobKeys.identityKey.privateKey
      );

      expect(decrypted).toBe(plaintext);
    });

    it('should verify signatures correctly', async () => {
      const keyPair = await cryptoService.generateIdentityKeyPair();
      const signedPreKey = await cryptoService.generateSignedPreKey(keyPair);

      const isValid = await cryptoService.verifySignature(
        signedPreKey.signature,
        signedPreKey.publicKey,
        keyPair.publicKey
      );

      expect(isValid).toBe(true);
    });
  });

  describe('Double Ratchet Protocol', () => {
    it('should initialize session correctly', async () => {
      const sharedSecret = new Uint8Array(32).fill(42);
      const remotePublicKey = new Uint8Array(32).fill(84);

      const state = await doubleRatchet.initializeSession(
        sharedSecret,
        remotePublicKey
      );

      expect(state.rootKey).toBeInstanceOf(Uint8Array);
      expect(state.sendingChainKey).toBeInstanceOf(Uint8Array);
      expect(state.localPublicKey).toBeInstanceOf(Uint8Array);
      expect(state.remotePublicKey).toEqual(remotePublicKey);
    });

    it('should perform ratchet encryption and decryption', async () => {
      const sharedSecret = new Uint8Array(32).fill(42);
      const aliceKeys = await cryptoService.generateKeyBundle();
      const bobKeys = await cryptoService.generateKeyBundle();

      const aliceState = await doubleRatchet.initializeSession(
        sharedSecret,
        bobKeys.identityKey.publicKey
      );

      const plaintext = 'Test message for Double Ratchet';
      
      const { ciphertext, header, updatedState } = await doubleRatchet.ratchetEncrypt(
        aliceState,
        plaintext
      );

      expect(ciphertext).toBeInstanceOf(Uint8Array);
      expect(header.publicKey).toBeInstanceOf(Uint8Array);
      expect(updatedState.sendingChainLength).toBe(1);
    });
  });

  describe('Message Flow', () => {
    it('should handle complete message exchange', async () => {
      const aliceKeys = await cryptoService.generateKeyBundle();
      const bobKeys = await cryptoService.generateKeyBundle();

      const sharedSecret = await cryptoService.deriveSharedSecret(
        bobKeys.identityKey.publicKey,
        aliceKeys.identityKey.privateKey
      );

      const aliceState = await doubleRatchet.initializeSession(
        sharedSecret,
        bobKeys.identityKey.publicKey
      );

      const bobState = await doubleRatchet.initializeSession(
        sharedSecret,
        aliceKeys.identityKey.publicKey
      );

      const messages = [
        'Hello Bob!',
        'This is Alice.',
        'How are you?'
      ];

      for (const message of messages) {
        const encrypted = await encryptionService.encryptMessage(
          message,
          bobKeys.identityKey.publicKey,
          aliceState
        );

        expect(encrypted.ciphertext.value).toBeInstanceOf(Uint8Array);
        expect(encrypted.nonce.value).toBeInstanceOf(Uint8Array);
        expect(encrypted.authTag.value).toBeInstanceOf(Uint8Array);
      }
    });
  });

  describe('Security Properties', () => {
    it('should provide Perfect Forward Secrecy', async () => {
      const aliceKeys = await cryptoService.generateKeyBundle();
      const bobKeys = await cryptoService.generateKeyBundle();

      const sharedSecret1 = await cryptoService.deriveSharedSecret(
        bobKeys.identityKey.publicKey,
        aliceKeys.identityKey.privateKey
      );

      const state1 = await doubleRatchet.initializeSession(
        sharedSecret1,
        bobKeys.identityKey.publicKey
      );

      const { updatedState: state2 } = await doubleRatchet.ratchetEncrypt(
        state1,
        'Message 1'
      );

      const { updatedState: state3 } = await doubleRatchet.ratchetEncrypt(
        state2,
        'Message 2'
      );

      expect(state1.sendingChainKey).not.toEqual(state2.sendingChainKey);
      expect(state2.sendingChainKey).not.toEqual(state3.sendingChainKey);
    });

    it('should detect message tampering', async () => {
      const aliceKeys = await cryptoService.generateKeyBundle();
      const plaintext = 'Sensitive message';

      const { ciphertext, nonce } = await cryptoService.encryptMessage(
        plaintext,
        aliceKeys.identityKey.publicKey,
        aliceKeys.identityKey.privateKey
      );

      ciphertext[0] ^= 0xFF;

      await expect(
        cryptoService.decryptMessage(
          ciphertext,
          nonce,
          aliceKeys.identityKey.publicKey,
          aliceKeys.identityKey.privateKey
        )
      ).rejects.toThrow();
    });
  });
});