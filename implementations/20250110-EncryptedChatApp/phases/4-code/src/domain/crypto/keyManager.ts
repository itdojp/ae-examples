import sodium from 'libsodium-wrappers';
import { v4 as uuidv4 } from 'uuid';
import { 
  IdentityKeyPair, 
  SignedPreKey, 
  OneTimePreKey,
  User
} from '../entities';

export class KeyManager {
  private static instance: KeyManager;

  private constructor() {}

  static async getInstance(): Promise<KeyManager> {
    if (!KeyManager.instance) {
      await sodium.ready;
      KeyManager.instance = new KeyManager();
    }
    return KeyManager.instance;
  }

  generateIdentityKeyPair(userId: string): IdentityKeyPair {
    const keyPair = sodium.crypto_sign_keypair();
    
    return {
      publicKey: sodium.to_base64(keyPair.publicKey),
      privateKey: sodium.to_base64(keyPair.privateKey),
      userId,
      createdAt: new Date(),
    };
  }

  generateSignedPreKey(userId: string, identityPrivateKey: string, keyId: number): SignedPreKey {
    const keyPair = sodium.crypto_box_keypair();
    const privateKey = sodium.from_base64(identityPrivateKey);
    
    const signature = sodium.crypto_sign_detached(
      keyPair.publicKey,
      privateKey
    );
    
    const expiresAt = new Date();
    expiresAt.setDate(expiresAt.getDate() + 30); // Expires in 30 days
    
    return {
      id: keyId,
      publicKey: sodium.to_base64(keyPair.publicKey),
      privateKey: sodium.to_base64(keyPair.privateKey),
      signature: sodium.to_base64(signature),
      userId,
      createdAt: new Date(),
      expiresAt,
    };
  }

  generateOneTimePreKeys(userId: string, startId: number, count: number): OneTimePreKey[] {
    const keys: OneTimePreKey[] = [];
    
    for (let i = 0; i < count; i++) {
      const keyPair = sodium.crypto_box_keypair();
      
      keys.push({
        id: startId + i,
        publicKey: sodium.to_base64(keyPair.publicKey),
        privateKey: sodium.to_base64(keyPair.privateKey),
        userId,
        used: false,
        createdAt: new Date(),
      });
    }
    
    return keys;
  }

  verifySignedPreKey(
    signedPreKeyPublic: string,
    signature: string,
    identityPublicKey: string
  ): boolean {
    try {
      const publicKey = sodium.from_base64(signedPreKeyPublic);
      const sig = sodium.from_base64(signature);
      const identityKey = sodium.from_base64(identityPublicKey);
      
      return sodium.crypto_sign_verify_detached(sig, publicKey, identityKey);
    } catch {
      return false;
    }
  }

  generateX25519KeyPair(): { publicKey: string; privateKey: string } {
    const keyPair = sodium.crypto_box_keypair();
    
    return {
      publicKey: sodium.to_base64(keyPair.publicKey),
      privateKey: sodium.to_base64(keyPair.privateKey),
    };
  }

  performX3DH(
    ourIdentityPrivate: string,
    ourEphemeralPrivate: string,
    theirIdentityPublic: string,
    theirSignedPreKeyPublic: string,
    theirOneTimePreKeyPublic?: string
  ): Uint8Array {
    const ourIdentity = sodium.from_base64(ourIdentityPrivate);
    const ourEphemeral = sodium.from_base64(ourEphemeralPrivate);
    const theirIdentity = sodium.from_base64(theirIdentityPublic);
    const theirSignedPreKey = sodium.from_base64(theirSignedPreKeyPublic);
    
    // DH1: ourIdentity x theirSignedPreKey
    const dh1 = sodium.crypto_scalarmult(
      ourIdentity.slice(0, 32),
      theirSignedPreKey
    );
    
    // DH2: ourEphemeral x theirIdentity
    const dh2 = sodium.crypto_scalarmult(
      ourEphemeral,
      theirIdentity.slice(0, 32)
    );
    
    // DH3: ourEphemeral x theirSignedPreKey
    const dh3 = sodium.crypto_scalarmult(
      ourEphemeral,
      theirSignedPreKey
    );
    
    let sharedSecret: Uint8Array;
    
    if (theirOneTimePreKeyPublic) {
      const theirOneTimePreKey = sodium.from_base64(theirOneTimePreKeyPublic);
      
      // DH4: ourEphemeral x theirOneTimePreKey
      const dh4 = sodium.crypto_scalarmult(
        ourEphemeral,
        theirOneTimePreKey
      );
      
      // Combine all DH outputs
      sharedSecret = new Uint8Array(dh1.length + dh2.length + dh3.length + dh4.length);
      sharedSecret.set(dh1);
      sharedSecret.set(dh2, dh1.length);
      sharedSecret.set(dh3, dh1.length + dh2.length);
      sharedSecret.set(dh4, dh1.length + dh2.length + dh3.length);
    } else {
      // Combine DH outputs without one-time pre-key
      sharedSecret = new Uint8Array(dh1.length + dh2.length + dh3.length);
      sharedSecret.set(dh1);
      sharedSecret.set(dh2, dh1.length);
      sharedSecret.set(dh3, dh1.length + dh2.length);
    }
    
    // Derive root key from shared secret
    const rootKey = sodium.crypto_kdf_derive_from_key(
      32,
      1,
      'X3DH_RK',
      sodium.crypto_generichash(32, sharedSecret)
    );
    
    return rootKey;
  }

  generateSafetyNumber(
    userAIdentityKey: string,
    userBIdentityKey: string
  ): string {
    const combined = userAIdentityKey < userBIdentityKey
      ? userAIdentityKey + userBIdentityKey
      : userBIdentityKey + userAIdentityKey;
    
    const hash = sodium.crypto_generichash(32, combined);
    const hex = sodium.to_hex(hash);
    
    // Format as groups of 5 digits for readability
    const digits = hex.replace(/[^0-9]/g, '').slice(0, 60);
    const groups = [];
    for (let i = 0; i < digits.length; i += 5) {
      groups.push(digits.slice(i, i + 5));
    }
    
    return groups.join(' ');
  }

  encryptMessage(
    plaintext: string,
    key: Uint8Array
  ): { ciphertext: string; nonce: string; authTag: string } {
    const nonce = sodium.randombytes_buf(sodium.crypto_aead_xchacha20poly1305_ietf_NPUBBYTES);
    const message = new TextEncoder().encode(plaintext);
    
    const ciphertext = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(
      message,
      null,
      null,
      nonce,
      key
    );
    
    // Extract auth tag (last 16 bytes)
    const authTag = ciphertext.slice(-16);
    const actualCiphertext = ciphertext.slice(0, -16);
    
    return {
      ciphertext: sodium.to_base64(actualCiphertext),
      nonce: sodium.to_base64(nonce),
      authTag: sodium.to_base64(authTag),
    };
  }

  decryptMessage(
    ciphertext: string,
    nonce: string,
    authTag: string,
    key: Uint8Array
  ): string {
    const ciphertextBytes = sodium.from_base64(ciphertext);
    const nonceBytes = sodium.from_base64(nonce);
    const authTagBytes = sodium.from_base64(authTag);
    
    // Combine ciphertext and auth tag
    const combined = new Uint8Array(ciphertextBytes.length + authTagBytes.length);
    combined.set(ciphertextBytes);
    combined.set(authTagBytes, ciphertextBytes.length);
    
    const plaintext = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(
      null,
      combined,
      null,
      nonceBytes,
      key
    );
    
    return new TextDecoder().decode(plaintext);
  }

  deriveKey(password: string, salt: string): Uint8Array {
    const saltBytes = sodium.from_base64(salt);
    
    return sodium.crypto_pwhash(
      32,
      password,
      saltBytes,
      sodium.crypto_pwhash_OPSLIMIT_INTERACTIVE,
      sodium.crypto_pwhash_MEMLIMIT_INTERACTIVE,
      sodium.crypto_pwhash_ALG_ARGON2ID13
    );
  }

  generateSalt(): string {
    return sodium.to_base64(
      sodium.randombytes_buf(sodium.crypto_pwhash_SALTBYTES)
    );
  }

  hashPassword(password: string): string {
    return sodium.crypto_pwhash_str(
      password,
      sodium.crypto_pwhash_OPSLIMIT_INTERACTIVE,
      sodium.crypto_pwhash_MEMLIMIT_INTERACTIVE
    );
  }

  verifyPassword(password: string, hash: string): boolean {
    return sodium.crypto_pwhash_str_verify(hash, password);
  }

  generateSecureRandom(bytes: number = 32): string {
    return sodium.to_base64(sodium.randombytes_buf(bytes));
  }

  clearMemory(data: Uint8Array): void {
    sodium.memzero(data);
  }
}