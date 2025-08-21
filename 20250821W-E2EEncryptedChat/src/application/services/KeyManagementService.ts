import { UserId } from '../../domain/entities/User';
import { CryptoKeyBundle, PreKeyBundle } from '../../domain/entities/CryptoKey';
import { KeyRepository } from '../../domain/repositories/KeyRepository';
import { CryptoService } from '../../infrastructure/crypto/CryptoService';

export interface KeyManagementService {
  generateKeyBundle(): Promise<CryptoKeyBundle>;
  rotateKeys(userId: UserId): Promise<void>;
  fetchPreKeys(userId: UserId): Promise<PreKeyBundle>;
  verifyKeySignature(key: any): Promise<boolean>;
}

export class KeyManagementServiceImpl implements KeyManagementService {
  private cryptoService: CryptoService;

  constructor(
    private keyRepository: KeyRepository
  ) {
    this.cryptoService = CryptoService.getInstance();
  }

  async generateKeyBundle(): Promise<CryptoKeyBundle> {
    await this.cryptoService.init();
    return await this.cryptoService.generateKeyBundle();
  }

  async rotateKeys(userId: UserId): Promise<void> {
    const currentBundle = await this.keyRepository.getKeyBundle(userId);
    if (!currentBundle) {
      throw new Error('No existing key bundle found for user');
    }

    const newSignedPreKey = await this.cryptoService.generateSignedPreKey(
      currentBundle.identityKey
    );

    const updatedBundle: CryptoKeyBundle = {
      ...currentBundle,
      signedPreKey: newSignedPreKey
    };

    await this.keyRepository.updateSignedPreKey(userId, updatedBundle);
    
    const oneTimePreKeyCount = await this.keyRepository.getOneTimePreKeyCount(userId);
    if (oneTimePreKeyCount < 20) {
      const newOneTimePreKeys = await this.cryptoService.generateOneTimePreKeys(80);
      await this.keyRepository.addOneTimePreKeys(userId, newOneTimePreKeys);
    }
  }

  async fetchPreKeys(userId: UserId): Promise<PreKeyBundle> {
    const bundle = await this.keyRepository.getPreKeyBundle(userId);
    if (!bundle) {
      throw new Error('No key bundle found for user');
    }
    return bundle;
  }

  async verifyKeySignature(signedPreKey: any): Promise<boolean> {
    if (!signedPreKey.publicKey || !signedPreKey.signature) {
      return false;
    }

    return await this.cryptoService.verifySignature(
      signedPreKey.signature,
      signedPreKey.publicKey,
      signedPreKey.publicKey
    );
  }

  async initializeUserKeys(userId: UserId): Promise<CryptoKeyBundle> {
    const keyBundle = await this.generateKeyBundle();
    await this.keyRepository.saveKeyBundle(userId, keyBundle);
    return keyBundle;
  }

  async refreshOneTimePreKeys(userId: UserId): Promise<void> {
    const count = await this.keyRepository.getOneTimePreKeyCount(userId);
    
    if (count < 10) {
      const newKeys = await this.cryptoService.generateOneTimePreKeys(100);
      await this.keyRepository.addOneTimePreKeys(userId, newKeys);
    }
  }
}