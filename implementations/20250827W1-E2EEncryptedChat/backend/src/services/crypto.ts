import nacl from 'tweetnacl';
import util from 'tweetnacl-util';
import { KeyPair } from '@e2e-chat/shared';

export class CryptoService {
  // Generate a new key pair for user
  static generateKeyPair(): KeyPair {
    const keyPair = nacl.box.keyPair();
    return {
      publicKey: util.encodeBase64(keyPair.publicKey),
      privateKey: util.encodeBase64(keyPair.secretKey)
    };
  }

  // Encrypt message using recipient's public key
  static encrypt(message: string, recipientPublicKey: string, senderPrivateKey: string): {
    ciphertext: string;
    nonce: string;
  } {
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

  // Decrypt message using recipient's private key
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

  // Generate ephemeral key for Perfect Forward Secrecy
  static generateEphemeralKey(): KeyPair {
    return this.generateKeyPair();
  }

  // Generate pre-keys for asynchronous key exchange
  static generatePreKeys(count: number = 100): string[] {
    const preKeys: string[] = [];
    for (let i = 0; i < count; i++) {
      const keyPair = nacl.box.keyPair();
      preKeys.push(util.encodeBase64(keyPair.publicKey));
    }
    return preKeys;
  }

  // Calculate security fingerprint for verification
  static calculateFingerprint(publicKey1: string, publicKey2: string): string {
    const combined = publicKey1 + publicKey2;
    const hash = nacl.hash(util.decodeUTF8(combined));
    const fingerprint = util.encodeBase64(hash).substring(0, 16);
    return fingerprint.match(/.{1,4}/g)?.join(' ') || fingerprint;
  }

  // Verify message authenticity
  static verifyMessage(message: string, signature: string, publicKey: string): boolean {
    try {
      const messageBytes = util.decodeUTF8(message);
      const signatureBytes = util.decodeBase64(signature);
      const publicKeyBytes = util.decodeBase64(publicKey);

      return nacl.sign.detached.verify(messageBytes, signatureBytes, publicKeyBytes);
    } catch {
      return false;
    }
  }

  // Sign message
  static signMessage(message: string, privateKey: string): string {
    const messageBytes = util.decodeUTF8(message);
    const privateKeyBytes = util.decodeBase64(privateKey);
    const signature = nacl.sign.detached(messageBytes, privateKeyBytes);
    return util.encodeBase64(signature);
  }
}