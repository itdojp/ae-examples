import { configureStore } from '@reduxjs/toolkit'
import authReducer from './slices/authSlice'
import chatReducer from './slices/chatSlice'
import settingsReducer from './slices/settingsSlice'
import encryptionReducer from './slices/encryptionSlice'

export const store = configureStore({
  reducer: {
    auth: authReducer,
    chat: chatReducer,
    settings: settingsReducer,
    encryption: encryptionReducer,
  },
  middleware: (getDefaultMiddleware) =>
    getDefaultMiddleware({
      serializableCheck: {
        ignoredActions: [
          'encryption/setKeyPair',
          'encryption/setPreKeys',
          'chat/addMessage',
        ],
        ignoredPaths: [
          'encryption.keyPair',
          'encryption.preKeys',
          'chat.messages.encryptedContent',
        ],
      },
    }),
})

export type RootState = ReturnType<typeof store.getState>
export type AppDispatch = typeof store.dispatch