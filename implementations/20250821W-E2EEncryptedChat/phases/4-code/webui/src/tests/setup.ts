import '@testing-library/jest-dom';
import { configure } from '@testing-library/react';

// Configure React Testing Library
configure({ testIdAttribute: 'data-testid' });

// Mock WebSocket
global.WebSocket = jest.fn(() => ({
  close: jest.fn(),
  send: jest.fn(),
  addEventListener: jest.fn(),
  removeEventListener: jest.fn(),
}));

// Mock WebCrypto API
Object.defineProperty(global, 'crypto', {
  value: {
    getRandomValues: jest.fn((arr) => arr.map(() => Math.floor(Math.random() * 256))),
    subtle: {
      generateKey: jest.fn(),
      encrypt: jest.fn(),
      decrypt: jest.fn(),
      importKey: jest.fn(),
      exportKey: jest.fn(),
    },
  },
});

// Mock IndexedDB
const FDBFactory = require('fake-indexeddb/lib/FDBFactory');
const FDBKeyRange = require('fake-indexeddb/lib/FDBKeyRange');
global.indexedDB = new FDBFactory();
global.IDBKeyRange = FDBKeyRange;

// Suppress console warnings in tests
const originalWarn = console.warn;
console.warn = (message) => {
  if (message.includes('React Router')) return;
  if (message.includes('Material-UI')) return;
  originalWarn(message);
};