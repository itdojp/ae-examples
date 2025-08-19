import { describe, it, expect } from 'vitest';
import { Nonce } from '../../../src/domain/value-objects/Nonce';

describe('Nonce', () => {
  describe('constructor', () => {
    it('should create a valid Nonce with correct length', () => {
      const data = new Uint8Array(12);
      const nonce = new Nonce(data);
      expect(nonce).toBeInstanceOf(Nonce);
    });

    it('should throw error for invalid length', () => {
      const data = new Uint8Array(11);
      expect(() => new Nonce(data)).toThrow('Nonce must be 12 bytes');
    });
  });

  describe('generate', () => {
    it('should generate a random nonce', () => {
      const nonce1 = Nonce.generate();
      const nonce2 = Nonce.generate();
      
      expect(nonce1).toBeInstanceOf(Nonce);
      expect(nonce2).toBeInstanceOf(Nonce);
      expect(nonce1.equals(nonce2)).toBe(false);
    });

    it('should generate nonce with correct length', () => {
      const nonce = Nonce.generate();
      const array = nonce.toUint8Array();
      expect(array.length).toBe(12);
    });
  });

  describe('toBase64 and fromBase64', () => {
    it('should convert to and from base64', () => {
      const nonce = Nonce.generate();
      const base64 = nonce.toBase64();
      
      const restored = Nonce.fromBase64(base64);
      expect(restored.equals(nonce)).toBe(true);
    });
  });

  describe('equals', () => {
    it('should return true for equal nonces', () => {
      const data = new Uint8Array(12).fill(42);
      const n1 = new Nonce(data);
      const n2 = new Nonce(data);
      expect(n1.equals(n2)).toBe(true);
    });

    it('should return false for different nonces', () => {
      const data1 = new Uint8Array(12).fill(42);
      const data2 = new Uint8Array(12).fill(43);
      const n1 = new Nonce(data1);
      const n2 = new Nonce(data2);
      expect(n1.equals(n2)).toBe(false);
    });
  });
});