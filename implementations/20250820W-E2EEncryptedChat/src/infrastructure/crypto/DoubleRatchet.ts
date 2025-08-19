import * as sodium from 'libsodium-wrappers';
import { DoubleRatchetState, MessageKey } from '../../domain/entities/Session';
import { CryptoService } from './CryptoService';

export class DoubleRatchet {
  private cryptoService: CryptoService;
  private readonly MAX_SKIP = 1000;
  private skippedMessageKeys: Map<string, MessageKey> = new Map();

  constructor() {
    this.cryptoService = CryptoService.getInstance();
  }

  async init(): Promise<void> {
    await sodium.ready;
    await this.cryptoService.init();
  }

  async initializeSession(
    sharedSecret: Uint8Array,
    remotePublicKey: Uint8Array
  ): Promise<DoubleRatchetState> {
    await this.init();
    
    const keyPair = sodium.crypto_box_keypair();
    const rootKey = await this.kdfRootKey(sharedSecret, remotePublicKey);
    const sendingChainKey = await this.kdfChainKey(rootKey);
    
    return {
      rootKey,
      sendingChainKey,
      receivingChainKey: new Uint8Array(32),
      sendingChainLength: 0,
      receivingChainLength: 0,
      previousSendingChainLength: 0,
      remotePublicKey,
      localPublicKey: keyPair.publicKey,
      localPrivateKey: keyPair.privateKey
    };
  }

  async ratchetEncrypt(
    state: DoubleRatchetState,
    plaintext: string
  ): Promise<{ 
    ciphertext: Uint8Array; 
    header: RatchetHeader;
    updatedState: DoubleRatchetState 
  }> {
    await this.init();
    
    const messageKey = await this.deriveMessageKey(state.sendingChainKey);
    const newChainKey = await this.kdfChainKey(state.sendingChainKey);
    
    const nonce = sodium.randombytes_buf(sodium.crypto_secretbox_NONCEBYTES);
    const message = sodium.from_string(plaintext);
    const ciphertext = sodium.crypto_secretbox_easy(message, nonce, messageKey);
    
    const header: RatchetHeader = {
      publicKey: state.localPublicKey,
      previousChainLength: state.previousSendingChainLength,
      messageNumber: state.sendingChainLength,
      nonce
    };
    
    const updatedState: DoubleRatchetState = {
      ...state,
      sendingChainKey: newChainKey,
      sendingChainLength: state.sendingChainLength + 1
    };
    
    return { ciphertext, header, updatedState };
  }

  async ratchetDecrypt(
    state: DoubleRatchetState,
    header: RatchetHeader,
    ciphertext: Uint8Array
  ): Promise<{ 
    plaintext: string; 
    updatedState: DoubleRatchetState 
  }> {
    await this.init();
    
    let updatedState = { ...state };
    
    if (!this.arraysEqual(header.publicKey, state.remotePublicKey)) {
      updatedState = await this.dhRatchet(updatedState, header);
    }
    
    updatedState = await this.skipMessageKeys(
      updatedState,
      header.messageNumber
    );
    
    const messageKey = await this.deriveMessageKey(updatedState.receivingChainKey);
    const newChainKey = await this.kdfChainKey(updatedState.receivingChainKey);
    
    const decrypted = sodium.crypto_secretbox_open_easy(
      ciphertext,
      header.nonce,
      messageKey
    );
    
    updatedState.receivingChainKey = newChainKey;
    updatedState.receivingChainLength += 1;
    
    return {
      plaintext: sodium.to_string(decrypted),
      updatedState
    };
  }

  private async dhRatchet(
    state: DoubleRatchetState,
    header: RatchetHeader
  ): Promise<DoubleRatchetState> {
    state.previousSendingChainLength = state.sendingChainLength;
    state.receivingChainLength = 0;
    state.sendingChainLength = 0;
    state.remotePublicKey = header.publicKey;
    
    const dhReceive = await this.cryptoService.deriveSharedSecret(
      state.remotePublicKey,
      state.localPrivateKey
    );
    
    const [newRootKey, newReceivingChainKey] = await this.kdfRootKeyPair(
      state.rootKey,
      dhReceive
    );
    
    const keyPair = sodium.crypto_box_keypair();
    state.localPublicKey = keyPair.publicKey;
    state.localPrivateKey = keyPair.privateKey;
    
    const dhSend = await this.cryptoService.deriveSharedSecret(
      state.remotePublicKey,
      state.localPrivateKey
    );
    
    const [finalRootKey, newSendingChainKey] = await this.kdfRootKeyPair(
      newRootKey,
      dhSend
    );
    
    state.rootKey = finalRootKey;
    state.receivingChainKey = newReceivingChainKey;
    state.sendingChainKey = newSendingChainKey;
    
    return state;
  }

  private async skipMessageKeys(
    state: DoubleRatchetState,
    until: number
  ): Promise<DoubleRatchetState> {
    if (state.receivingChainLength + this.MAX_SKIP < until) {
      throw new Error('Too many skipped messages');
    }
    
    while (state.receivingChainLength < until) {
      const messageKey = await this.deriveMessageKey(state.receivingChainKey);
      const key = `${sodium.to_base64(state.remotePublicKey)}-${state.receivingChainLength}`;
      this.skippedMessageKeys.set(key, messageKey);
      
      state.receivingChainKey = await this.kdfChainKey(state.receivingChainKey);
      state.receivingChainLength += 1;
    }
    
    return state;
  }

  private async kdfRootKey(
    rootKey: Uint8Array,
    dhOutput: Uint8Array
  ): Promise<Uint8Array> {
    const info = sodium.from_string('DoubleRatchet');
    const input = new Uint8Array(rootKey.length + dhOutput.length);
    input.set(rootKey);
    input.set(dhOutput, rootKey.length);
    
    return await this.cryptoService.hash(input);
  }

  private async kdfRootKeyPair(
    rootKey: Uint8Array,
    dhOutput: Uint8Array
  ): Promise<[Uint8Array, Uint8Array]> {
    const info = sodium.from_string('DoubleRatchetPair');
    const input = new Uint8Array(rootKey.length + dhOutput.length);
    input.set(rootKey);
    input.set(dhOutput, rootKey.length);
    
    const hash = await this.cryptoService.hash(input);
    const newRootKey = hash.slice(0, 32);
    const chainKey = hash.slice(32, 64);
    
    return [newRootKey, chainKey];
  }

  private async kdfChainKey(chainKey: Uint8Array): Promise<Uint8Array> {
    const constant = sodium.from_string('chain');
    return await this.cryptoService.generateHMAC(chainKey, constant);
  }

  private async deriveMessageKey(chainKey: Uint8Array): Promise<MessageKey> {
    const constant = sodium.from_string('message');
    return await this.cryptoService.generateHMAC(chainKey, constant);
  }

  private arraysEqual(a: Uint8Array, b: Uint8Array): boolean {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }
}

export interface RatchetHeader {
  publicKey: Uint8Array;
  previousChainLength: number;
  messageNumber: number;
  nonce: Uint8Array;
}