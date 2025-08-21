/**
 * Simple tests to verify basic functionality
 */

import { describe, test, expect } from '@jest/globals';

describe('Basic Tests', () => {
  test('should pass basic assertion', () => {
    expect(1 + 1).toBe(2);
  });

  test('should handle arrays', () => {
    const arr = [1, 2, 3];
    expect(arr).toHaveLength(3);
    expect(arr).toContain(2);
  });

  test('should handle objects', () => {
    const obj = { name: 'test', value: 42 };
    expect(obj.name).toBe('test');
    expect(obj.value).toBe(42);
  });
});