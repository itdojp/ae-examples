export class CipherText {
  constructor(private readonly value: Uint8Array) {
    if (value.length < 16) {
      throw new Error('Invalid ciphertext length: minimum 16 bytes required');
    }
  }

  toBase64(): string {
    return Buffer.from(this.value).toString('base64');
  }

  static fromBase64(base64: string): CipherText {
    const buffer = Buffer.from(base64, 'base64');
    return new CipherText(new Uint8Array(buffer));
  }

  toUint8Array(): Uint8Array {
    return this.value;
  }

  equals(other: CipherText): boolean {
    if (this.value.length !== other.value.length) {
      return false;
    }
    for (let i = 0; i < this.value.length; i++) {
      if (this.value[i] !== other.value[i]) {
        return false;
      }
    }
    return true;
  }
}