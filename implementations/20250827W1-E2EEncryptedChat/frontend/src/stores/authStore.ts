import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { User, KeyPair } from '@e2e-chat/shared';

interface AuthState {
  token: string | null;
  user: User | null;
  keyPair: KeyPair | null;
  setAuth: (token: string, user: User, keyPair?: KeyPair) => void;
  logout: () => void;
}

export const useAuthStore = create<AuthState>()(
  persist(
    (set) => ({
      token: null,
      user: null,
      keyPair: null,
      setAuth: (token, user, keyPair) => set({ token, user, keyPair }),
      logout: () => set({ token: null, user: null, keyPair: null })
    }),
    {
      name: 'auth-storage'
    }
  )
);