export class SecurityNumber {
  constructor(
    private readonly localFingerprint: string,
    private readonly remoteFingerprint: string
  ) {
    if (!localFingerprint || !remoteFingerprint) {
      throw new Error('Both local and remote fingerprints are required');
    }
  }

  verify(other: SecurityNumber): boolean {
    return (
      this.localFingerprint === other.remoteFingerprint &&
      this.remoteFingerprint === other.localFingerprint
    );
  }

  toQRCode(): string {
    return `${this.localFingerprint}:${this.remoteFingerprint}`;
  }

  static fromQRCode(qrCode: string): SecurityNumber {
    const parts = qrCode.split(':');
    if (parts.length !== 2) {
      throw new Error('Invalid QR code format');
    }
    return new SecurityNumber(parts[0], parts[1]);
  }

  getLocalFingerprint(): string {
    return this.localFingerprint;
  }

  getRemoteFingerprint(): string {
    return this.remoteFingerprint;
  }

  toString(): string {
    const formatFingerprint = (fp: string) => {
      const chunks = [];
      for (let i = 0; i < fp.length; i += 5) {
        chunks.push(fp.slice(i, i + 5));
      }
      return chunks.join(' ');
    };

    return `Local: ${formatFingerprint(this.localFingerprint)}\nRemote: ${formatFingerprint(this.remoteFingerprint)}`;
  }
}