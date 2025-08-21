import { describe, it, expect } from 'vitest';
import { CipherText } from '../../../src/domain/value-objects/CipherText';

describe('CipherText', () => {
  describe('constructor', () => {
    it('should create a valid CipherText with minimum length', () => {
      const data = new Uint8Array(16);
      const cipherText = new CipherText(data);
      expect(cipherText).toBeInstanceOf(CipherText);
    });

    it('should throw error for invalid length', () => {
      const data = new Uint8Array(15);
      expect(() => new CipherText(data)).toThrow('Invalid ciphertext length');
    });
  });

  describe('toBase64 and fromBase64', () => {
    it('should convert to and from base64', () => {
      const data = new Uint8Array([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
      const cipherText = new CipherText(data);
      const base64 = cipherText.toBase64();
      
      const restored = CipherText.fromBase64(base64);
      expect(restored.equals(cipherText)).toBe(true);
    });
  });

  describe('equals', () => {
    it('should return true for equal cipher texts', () => {
      const data = new Uint8Array(16).fill(42);
      const ct1 = new CipherText(data);
      const ct2 = new CipherText(data);
      expect(ct1.equals(ct2)).toBe(true);
    });

    it('should return false for different cipher texts', () => {
      const data1 = new Uint8Array(16).fill(42);
      const data2 = new Uint8Array(16).fill(43);
      const ct1 = new CipherText(data1);
      const ct2 = new CipherText(data2);
      expect(ct1.equals(ct2)).toBe(false);
    });

    it('should return false for different lengths', () => {
      const data1 = new Uint8Array(16);
      const data2 = new Uint8Array(32);
      const ct1 = new CipherText(data1);
      const ct2 = new CipherText(data2);
      expect(ct1.equals(ct2)).toBe(false);
    });
  });
});