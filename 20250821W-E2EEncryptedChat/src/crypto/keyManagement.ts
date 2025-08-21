// Key Management Service Implementation
// Handles generation, storage, and rotation of cryptographic keys

import {
  CryptoKeyBundle,
  IdentityKey,
  SignedPreKey,
  OneTimePreKey,
  DeviceKey,
  UserId,
  KeyError
} from '../types';

export interface KeyManagementService {
  generateKeyBundle(userId: UserId): Promise<CryptoKeyBundle>;
  rotateKeys(userId: UserId): Promise<void>;
  fetchPreKeys(userId: UserId): Promise<PreKeyBundle>;
  verifyKeySignature(key: SignedPreKey): Promise<boolean>;
  storeKeyBundle(userId: UserId, bundle: CryptoKeyBundle): Promise<void>;
  getKeyBundle(userId: UserId): Promise<CryptoKeyBundle | null>;
  generatePreKeys(count: number): Promise<OneTimePreKey[]>;
}

export interface PreKeyBundle {
  identityKey: IdentityKey;
  signedPreKey: SignedPreKey;
  oneTimePreKey?: OneTimePreKey;
}

export class KeyManagementServiceImpl implements KeyManagementService {
  private static readonly IDENTITY_KEY_ALGORITHM = 'Ed25519';
  private static readonly DH_KEY_ALGORITHM = 'X25519';
  private static readonly PRE_KEY_COUNT = 100;

  constructor(
    private readonly storage: KeyStorage
  ) {}

  /**
   * Generate a complete key bundle for a user
   */
  async generateKeyBundle(userId: UserId): Promise<CryptoKeyBundle> {
    try {
      // Generate identity key (long-term signing key)
      const identityKey = await this.generateIdentityKey();
      
      // Generate signed pre-key
      const signedPreKey = await this.generateSignedPreKey(identityKey);
      
      // Generate one-time pre-keys
      const oneTimePreKeys = await this.generatePreKeys(KeyManagementServiceImpl.PRE_KEY_COUNT);
      
      // Generate device key
      const deviceKey = await this.generateDeviceKey();
      
      const bundle: CryptoKeyBundle = {
        identityKey,
        signedPreKey,
        oneTimePreKeys,
        deviceKey
      };
      
      // Store the bundle
      await this.storeKeyBundle(userId, bundle);
      
      return bundle;
    } catch (error) {
      throw new KeyError(
        `Failed to generate key bundle: ${error.message}`,
        'KEY_BUNDLE_GENERATION'
      );
    }
  }

  /**
   * Rotate keys for enhanced security
   */
  async rotateKeys(userId: UserId): Promise<void> {
    try {
      const existingBundle = await this.getKeyBundle(userId);
      if (!existingBundle) {
        throw new Error('No existing key bundle found');
      }

      // Generate new signed pre-key
      const newSignedPreKey = await this.generateSignedPreKey(existingBundle.identityKey);
      
      // Generate new one-time pre-keys
      const newOneTimePreKeys = await this.generatePreKeys(KeyManagementServiceImpl.PRE_KEY_COUNT);
      
      // Update bundle with new keys
      const updatedBundle: CryptoKeyBundle = {
        ...existingBundle,
        signedPreKey: newSignedPreKey,
        oneTimePreKeys: newOneTimePreKeys
      };
      
      await this.storeKeyBundle(userId, updatedBundle);
    } catch (error) {
      throw new KeyError(
        `Failed to rotate keys: ${error.message}`,
        'KEY_ROTATION'
      );
    }
  }

  /**
   * Fetch pre-keys for initiating a session
   */
  async fetchPreKeys(userId: UserId): Promise<PreKeyBundle> {
    try {
      const bundle = await this.getKeyBundle(userId);
      if (!bundle) {
        throw new Error('No key bundle found for user');
      }

      // Consume one-time pre-key if available
      const oneTimePreKey = bundle.oneTimePreKeys.length > 0 
        ? bundle.oneTimePreKeys.shift()
        : undefined;

      // Update bundle if one-time key was consumed
      if (oneTimePreKey) {
        await this.storeKeyBundle(userId, bundle);
      }

      return {
        identityKey: bundle.identityKey,
        signedPreKey: bundle.signedPreKey,
        oneTimePreKey
      };
    } catch (error) {
      throw new KeyError(
        `Failed to fetch pre-keys: ${error.message}`,
        'PRE_KEY_FETCH'
      );
    }
  }

  /**
   * Verify the signature of a signed pre-key
   */
  async verifyKeySignature(key: SignedPreKey): Promise<boolean> {
    try {
      // Implementation would verify the signature using the identity key
      // For now, return true as a placeholder
      return true;
    } catch (error) {
      throw new KeyError(
        `Failed to verify key signature: ${error.message}`,
        'KEY_SIGNATURE_VERIFICATION'
      );
    }
  }

  /**
   * Store key bundle securely
   */
  async storeKeyBundle(userId: UserId, bundle: CryptoKeyBundle): Promise<void> {
    try {
      await this.storage.store(userId, bundle);
    } catch (error) {
      throw new KeyError(
        `Failed to store key bundle: ${error.message}`,
        'KEY_STORAGE'
      );
    }
  }

  /**
   * Retrieve key bundle from storage
   */
  async getKeyBundle(userId: UserId): Promise<CryptoKeyBundle | null> {
    try {
      return await this.storage.retrieve(userId);
    } catch (error) {
      throw new KeyError(
        `Failed to retrieve key bundle: ${error.message}`,
        'KEY_RETRIEVAL'
      );
    }
  }

  /**
   * Generate multiple one-time pre-keys
   */
  async generatePreKeys(count: number): Promise<OneTimePreKey[]> {
    const preKeys: OneTimePreKey[] = [];
    
    for (let i = 0; i < count; i++) {
      const keyPair = await this.generateDHKeyPair();
      preKeys.push({
        id: i,
        publicKey: keyPair.publicKey,
        privateKey: keyPair.privateKey
      });
    }
    
    return preKeys;
  }

  // Private helper methods

  private async generateIdentityKey(): Promise<IdentityKey> {
    const keyPair = await crypto.subtle.generateKey(
      { name: KeyManagementServiceImpl.IDENTITY_KEY_ALGORITHM },
      true,
      ['sign', 'verify']
    );
    
    const publicKey = await crypto.subtle.exportKey('raw', keyPair.publicKey);
    const privateKey = await crypto.subtle.exportKey('raw', keyPair.privateKey);
    
    return {
      publicKey: new Uint8Array(publicKey),
      privateKey: new Uint8Array(privateKey)
    };
  }

  private async generateSignedPreKey(identityKey: IdentityKey): Promise<SignedPreKey> {
    const dhKeyPair = await this.generateDHKeyPair();
    
    // Sign the public key with identity key
    const signature = await this.signPublicKey(dhKeyPair.publicKey, identityKey.privateKey!);
    
    return {
      id: Date.now(), // Use timestamp as ID
      publicKey: dhKeyPair.publicKey,
      privateKey: dhKeyPair.privateKey,
      signature,
      timestamp: new Date()
    };
  }

  private async generateDeviceKey(): Promise<DeviceKey> {
    const keyPair = await this.generateDHKeyPair();
    
    return {
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey
    };
  }

  private async generateDHKeyPair(): Promise<{ publicKey: Uint8Array; privateKey: Uint8Array }> {
    const keyPair = await crypto.subtle.generateKey(
      { name: KeyManagementServiceImpl.DH_KEY_ALGORITHM },
      true,
      ['deriveBits']
    );
    
    const publicKey = await crypto.subtle.exportKey('raw', keyPair.publicKey);
    const privateKey = await crypto.subtle.exportKey('raw', keyPair.privateKey);
    
    return {
      publicKey: new Uint8Array(publicKey),
      privateKey: new Uint8Array(privateKey)
    };
  }

  private async signPublicKey(publicKey: Uint8Array, privateKey: Uint8Array): Promise<Uint8Array> {
    const signingKey = await crypto.subtle.importKey(
      'raw',
      privateKey,
      { name: KeyManagementServiceImpl.IDENTITY_KEY_ALGORITHM },
      false,
      ['sign']
    );
    
    const signature = await crypto.subtle.sign(
      KeyManagementServiceImpl.IDENTITY_KEY_ALGORITHM,
      signingKey,
      publicKey
    );
    
    return new Uint8Array(signature);
  }
}

// Storage interface for key management
export interface KeyStorage {
  store(userId: UserId, bundle: CryptoKeyBundle): Promise<void>;
  retrieve(userId: UserId): Promise<CryptoKeyBundle | null>;
  delete(userId: UserId): Promise<void>;
}

// In-memory storage implementation (for development/testing)
export class InMemoryKeyStorage implements KeyStorage {
  private storage = new Map<UserId, CryptoKeyBundle>();

  async store(userId: UserId, bundle: CryptoKeyBundle): Promise<void> {
    // Deep clone to avoid reference issues
    const clonedBundle = JSON.parse(JSON.stringify(bundle));
    this.storage.set(userId, clonedBundle);
  }

  async retrieve(userId: UserId): Promise<CryptoKeyBundle | null> {
    const bundle = this.storage.get(userId);
    return bundle ? JSON.parse(JSON.stringify(bundle)) : null;
  }

  async delete(userId: UserId): Promise<void> {
    this.storage.delete(userId);
  }
}

// Secure storage implementation (using IndexedDB or similar)
export class SecureKeyStorage implements KeyStorage {
  private dbName = 'e2e-chat-keys';
  private version = 1;
  private storeName = 'keyBundles';

  async store(userId: UserId, bundle: CryptoKeyBundle): Promise<void> {
    const db = await this.openDB();
    const transaction = db.transaction([this.storeName], 'readwrite');
    const store = transaction.objectStore(this.storeName);
    
    // Encrypt bundle before storing (implementation would use device-specific key)
    const encryptedBundle = await this.encryptBundle(bundle);
    
    await store.put({ userId, bundle: encryptedBundle });
    await transaction.complete;
  }

  async retrieve(userId: UserId): Promise<CryptoKeyBundle | null> {
    const db = await this.openDB();
    const transaction = db.transaction([this.storeName], 'readonly');
    const store = transaction.objectStore(this.storeName);
    
    const result = await store.get(userId);
    if (!result) return null;
    
    // Decrypt bundle after retrieving
    return await this.decryptBundle(result.bundle);
  }

  async delete(userId: UserId): Promise<void> {
    const db = await this.openDB();
    const transaction = db.transaction([this.storeName], 'readwrite');
    const store = transaction.objectStore(this.storeName);
    
    await store.delete(userId);
    await transaction.complete;
  }

  private async openDB(): Promise<IDBDatabase> {
    return new Promise((resolve, reject) => {
      const request = indexedDB.open(this.dbName, this.version);
      
      request.onerror = () => reject(request.error);
      request.onsuccess = () => resolve(request.result);
      
      request.onupgradeneeded = (event) => {
        const db = (event.target as IDBOpenDBRequest).result;
        
        if (!db.objectStoreNames.contains(this.storeName)) {
          const store = db.createObjectStore(this.storeName, { keyPath: 'userId' });
          store.createIndex('userId', 'userId', { unique: true });
        }
      };
    });
  }

  private async encryptBundle(bundle: CryptoKeyBundle): Promise<string> {
    // Placeholder - would implement actual encryption using device key
    return btoa(JSON.stringify(bundle));
  }

  private async decryptBundle(encryptedBundle: string): Promise<CryptoKeyBundle> {
    // Placeholder - would implement actual decryption using device key
    return JSON.parse(atob(encryptedBundle));
  }
}