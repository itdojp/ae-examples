export class Nonce {
  private static readonly NONCE_LENGTH = 12;

  constructor(private readonly value: Uint8Array) {
    if (value.length !== Nonce.NONCE_LENGTH) {
      throw new Error(`Nonce must be ${Nonce.NONCE_LENGTH} bytes`);
    }
  }

  static generate(): Nonce {
    const array = new Uint8Array(Nonce.NONCE_LENGTH);
    if (typeof window !== 'undefined' && window.crypto) {
      window.crypto.getRandomValues(array);
    } else {
      const crypto = require('crypto');
      crypto.randomFillSync(array);
    }
    return new Nonce(array);
  }

  toBase64(): string {
    return Buffer.from(this.value).toString('base64');
  }

  static fromBase64(base64: string): Nonce {
    const buffer = Buffer.from(base64, 'base64');
    return new Nonce(new Uint8Array(buffer));
  }

  toUint8Array(): Uint8Array {
    return this.value;
  }

  equals(other: Nonce): boolean {
    for (let i = 0; i < this.value.length; i++) {
      if (this.value[i] !== other.value[i]) {
        return false;
      }
    }
    return true;
  }
}