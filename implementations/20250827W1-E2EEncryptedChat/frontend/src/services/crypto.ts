import nacl from 'tweetnacl';
import util from 'tweetnacl-util';
import { KeyPair } from '@e2e-chat/shared';

export class CryptoService {
  static generateKeyPair(): KeyPair {
    const keyPair = nacl.box.keyPair();
    return {
      publicKey: util.encodeBase64(keyPair.publicKey),
      privateKey: util.encodeBase64(keyPair.secretKey)
    };
  }

  static encrypt(
    message: string,
    recipientPublicKey: string,
    senderPrivateKey: string
  ): { ciphertext: string; nonce: string } {
    const messageBytes = util.decodeUTF8(message);
    const nonce = nacl.randomBytes(nacl.box.nonceLength);
    const recipientKey = util.decodeBase64(recipientPublicKey);
    const senderKey = util.decodeBase64(senderPrivateKey);

    const encrypted = nacl.box(messageBytes, nonce, recipientKey, senderKey);

    return {
      ciphertext: util.encodeBase64(encrypted),
      nonce: util.encodeBase64(nonce)
    };
  }

  static decrypt(
    ciphertext: string,
    nonce: string,
    senderPublicKey: string,
    recipientPrivateKey: string
  ): string | null {
    try {
      const ciphertextBytes = util.decodeBase64(ciphertext);
      const nonceBytes = util.decodeBase64(nonce);
      const senderKey = util.decodeBase64(senderPublicKey);
      const recipientKey = util.decodeBase64(recipientPrivateKey);

      const decrypted = nacl.box.open(ciphertextBytes, nonceBytes, senderKey, recipientKey);

      if (!decrypted) {
        return null;
      }

      return util.encodeUTF8(decrypted);
    } catch (error) {
      console.error('Decryption failed:', error);
      return null;
    }
  }

  static calculateFingerprint(publicKey1: string, publicKey2: string): string {
    const combined = publicKey1 + publicKey2;
    const hash = nacl.hash(util.decodeUTF8(combined));
    const fingerprint = util.encodeBase64(hash).substring(0, 16);
    return fingerprint.match(/.{1,4}/g)?.join(' ') || fingerprint;
  }
}