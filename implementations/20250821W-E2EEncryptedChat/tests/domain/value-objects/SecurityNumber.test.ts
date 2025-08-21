import { describe, it, expect } from 'vitest';
import { SecurityNumber } from '../../../src/domain/value-objects/SecurityNumber';

describe('SecurityNumber', () => {
  describe('constructor', () => {
    it('should create a valid SecurityNumber', () => {
      const sn = new SecurityNumber('local123', 'remote456');
      expect(sn).toBeInstanceOf(SecurityNumber);
    });

    it('should throw error for missing fingerprints', () => {
      expect(() => new SecurityNumber('', 'remote')).toThrow('Both local and remote fingerprints are required');
      expect(() => new SecurityNumber('local', '')).toThrow('Both local and remote fingerprints are required');
    });
  });

  describe('verify', () => {
    it('should verify matching security numbers', () => {
      const alice = new SecurityNumber('alice123', 'bob456');
      const bob = new SecurityNumber('bob456', 'alice123');
      
      expect(alice.verify(bob)).toBe(true);
      expect(bob.verify(alice)).toBe(true);
    });

    it('should not verify mismatched security numbers', () => {
      const alice = new SecurityNumber('alice123', 'bob456');
      const bob = new SecurityNumber('bob789', 'alice999');
      
      expect(alice.verify(bob)).toBe(false);
      expect(bob.verify(alice)).toBe(false);
    });
  });

  describe('QR code operations', () => {
    it('should convert to and from QR code', () => {
      const sn = new SecurityNumber('local123', 'remote456');
      const qrCode = sn.toQRCode();
      
      expect(qrCode).toBe('local123:remote456');
      
      const restored = SecurityNumber.fromQRCode(qrCode);
      expect(restored.getLocalFingerprint()).toBe('local123');
      expect(restored.getRemoteFingerprint()).toBe('remote456');
    });

    it('should throw error for invalid QR code format', () => {
      expect(() => SecurityNumber.fromQRCode('invalid')).toThrow('Invalid QR code format');
      expect(() => SecurityNumber.fromQRCode('too:many:parts')).toThrow('Invalid QR code format');
    });
  });

  describe('toString', () => {
    it('should format fingerprints for display', () => {
      const sn = new SecurityNumber('1234567890ABCDEF', 'FEDCBA0987654321');
      const formatted = sn.toString();
      
      expect(formatted).toContain('Local: 12345 67890 ABCDE F');
      expect(formatted).toContain('Remote: FEDCB A0987 65432 1');
    });
  });
});