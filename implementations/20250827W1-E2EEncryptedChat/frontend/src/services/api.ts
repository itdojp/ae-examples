import axios from 'axios';
import { User, EncryptedMessage } from '@e2e-chat/shared';

const api = axios.create({
  baseURL: '/api'
});

// Add auth token to requests
api.interceptors.request.use((config) => {
  const token = localStorage.getItem('token');
  if (token) {
    config.headers.Authorization = `Bearer ${token}`;
  }
  return config;
});

export const authApi = {
  register: async (email: string, password: string, displayName: string) => {
    const response = await api.post('/auth/register', { email, password, displayName });
    return response.data;
  },

  login: async (email: string, password: string) => {
    const response = await api.post('/auth/login', { email, password });
    return response.data;
  },

  getMe: async () => {
    const response = await api.get('/auth/me');
    return response.data;
  },

  getUsers: async () => {
    const response = await api.get('/auth/users');
    return response.data;
  }
};

export const messagesApi = {
  send: async (recipientId: string, ciphertext: string, nonce: string, authTag: string, ephemeralKey?: string) => {
    const response = await api.post('/messages/send', {
      recipientId,
      ciphertext,
      nonce,
      authTag,
      ephemeralKey
    });
    return response.data;
  },

  getConversation: async (userId: string) => {
    const response = await api.get(`/messages/conversation/${userId}`);
    return response.data;
  },

  verifySession: async (sessionId: string, securityNumber: any) => {
    const response = await api.post('/messages/verify-session', {
      sessionId,
      securityNumber
    });
    return response.data;
  }
};

export const keysApi = {
  getKeys: async (userId: string) => {
    const response = await api.get(`/keys/${userId}`);
    return response.data;
  },

  rotateKeys: async () => {
    const response = await api.post('/keys/rotate');
    return response.data;
  }
};