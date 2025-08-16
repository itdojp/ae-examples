import { createSlice, createAsyncThunk, PayloadAction } from '@reduxjs/toolkit'
import { EncryptionService } from '../../services/encryptionService'

export interface KeyPair {
  publicKey: ArrayBuffer
  privateKey: ArrayBuffer
}

export interface PreKey {
  id: number
  keyPair: KeyPair
}

export interface SignedPreKey {
  id: number
  keyPair: KeyPair
  signature: ArrayBuffer
}

export interface EncryptionState {
  identityKeyPair: KeyPair | null
  signedPreKey: SignedPreKey | null
  preKeys: PreKey[]
  sessionKeys: { [contactId: string]: any } // Signal Protocol session
  isInitialized: boolean
  isLoading: boolean
  error: string | null
  keyRotationInterval: number // in hours
  lastKeyRotation: number // timestamp
}

const initialState: EncryptionState = {
  identityKeyPair: null,
  signedPreKey: null,
  preKeys: [],
  sessionKeys: {},
  isInitialized: false,
  isLoading: false,
  error: null,
  keyRotationInterval: 24 * 7, // 1 week
  lastKeyRotation: 0,
}

// Async Thunks
export const initializeEncryption = createAsyncThunk(
  'encryption/initialize',
  async (userId: string, { rejectWithValue }) => {
    try {
      const encryptionService = new EncryptionService()
      await encryptionService.initialize(userId)
      
      const identityKeyPair = await encryptionService.getIdentityKeyPair()
      const signedPreKey = await encryptionService.generateSignedPreKey()
      const preKeys = await encryptionService.generatePreKeys(10)
      
      return {
        identityKeyPair,
        signedPreKey,
        preKeys,
      }
    } catch (error: any) {
      return rejectWithValue(error.message || 'Failed to initialize encryption')
    }
  }
)

export const rotateKeys = createAsyncThunk(
  'encryption/rotateKeys',
  async (_, { getState, rejectWithValue }) => {
    try {
      const state = getState() as { encryption: EncryptionState }
      if (!state.encryption.isInitialized) {
        throw new Error('Encryption not initialized')
      }
      
      const encryptionService = new EncryptionService()
      const signedPreKey = await encryptionService.generateSignedPreKey()
      const preKeys = await encryptionService.generatePreKeys(10)
      
      return {
        signedPreKey,
        preKeys,
        timestamp: Date.now(),
      }
    } catch (error: any) {
      return rejectWithValue(error.message || 'Failed to rotate keys')
    }
  }
)

export const establishSession = createAsyncThunk(
  'encryption/establishSession',
  async (
    { contactId, keyBundle }: { contactId: string; keyBundle: any },
    { rejectWithValue }
  ) => {
    try {
      const encryptionService = new EncryptionService()
      const session = await encryptionService.createSession(contactId, keyBundle)
      
      return {
        contactId,
        session,
      }
    } catch (error: any) {
      return rejectWithValue(error.message || 'Failed to establish session')
    }
  }
)

export const encryptMessage = createAsyncThunk(
  'encryption/encryptMessage',
  async (
    { contactId, plaintext }: { contactId: string; plaintext: string },
    { getState, rejectWithValue }
  ) => {
    try {
      const state = getState() as { encryption: EncryptionState }
      const session = state.encryption.sessionKeys[contactId]
      
      if (!session) {
        throw new Error('No session established with contact')
      }
      
      const encryptionService = new EncryptionService()
      const encrypted = await encryptionService.encryptMessage(session, plaintext)
      
      return {
        contactId,
        encryptedContent: encrypted.ciphertext,
        nonce: encrypted.nonce,
        signature: encrypted.signature,
      }
    } catch (error: any) {
      return rejectWithValue(error.message || 'Failed to encrypt message')
    }
  }
)

export const decryptMessage = createAsyncThunk(
  'encryption/decryptMessage',
  async (
    {
      contactId,
      encryptedContent,
      nonce,
      signature,
    }: {
      contactId: string
      encryptedContent: ArrayBuffer
      nonce: ArrayBuffer
      signature: ArrayBuffer
    },
    { getState, rejectWithValue }
  ) => {
    try {
      const state = getState() as { encryption: EncryptionState }
      const session = state.encryption.sessionKeys[contactId]
      
      if (!session) {
        throw new Error('No session established with contact')
      }
      
      const encryptionService = new EncryptionService()
      const decrypted = await encryptionService.decryptMessage(session, {
        ciphertext: encryptedContent,
        nonce,
        signature,
      })
      
      return {
        contactId,
        plaintext: decrypted,
      }
    } catch (error: any) {
      return rejectWithValue(error.message || 'Failed to decrypt message')
    }
  }
)

const encryptionSlice = createSlice({
  name: 'encryption',
  initialState,
  reducers: {
    setKeyPair: (state, action: PayloadAction<KeyPair>) => {
      state.identityKeyPair = action.payload
    },
    
    setSignedPreKey: (state, action: PayloadAction<SignedPreKey>) => {
      state.signedPreKey = action.payload
    },
    
    setPreKeys: (state, action: PayloadAction<PreKey[]>) => {
      state.preKeys = action.payload
    },
    
    addSessionKey: (state, action: PayloadAction<{ contactId: string; session: any }>) => {
      const { contactId, session } = action.payload
      state.sessionKeys[contactId] = session
    },
    
    removeSessionKey: (state, action: PayloadAction<string>) => {
      const contactId = action.payload
      delete state.sessionKeys[contactId]
    },
    
    updateKeyRotationInterval: (state, action: PayloadAction<number>) => {
      state.keyRotationInterval = action.payload
    },
    
    clearError: (state) => {
      state.error = null
    },
    
    reset: (state) => {
      return { ...initialState }
    },
  },
  extraReducers: (builder) => {
    builder
      // Initialize Encryption
      .addCase(initializeEncryption.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(initializeEncryption.fulfilled, (state, action) => {
        state.isLoading = false
        state.identityKeyPair = action.payload.identityKeyPair
        state.signedPreKey = action.payload.signedPreKey
        state.preKeys = action.payload.preKeys
        state.isInitialized = true
        state.lastKeyRotation = Date.now()
      })
      .addCase(initializeEncryption.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Rotate Keys
      .addCase(rotateKeys.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(rotateKeys.fulfilled, (state, action) => {
        state.isLoading = false
        state.signedPreKey = action.payload.signedPreKey
        state.preKeys = action.payload.preKeys
        state.lastKeyRotation = action.payload.timestamp
      })
      .addCase(rotateKeys.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Establish Session
      .addCase(establishSession.fulfilled, (state, action) => {
        const { contactId, session } = action.payload
        state.sessionKeys[contactId] = session
      })
      .addCase(establishSession.rejected, (state, action) => {
        state.error = action.payload as string
      })
      
      // Encrypt Message
      .addCase(encryptMessage.rejected, (state, action) => {
        state.error = action.payload as string
      })
      
      // Decrypt Message
      .addCase(decryptMessage.rejected, (state, action) => {
        state.error = action.payload as string
      })
  },
})

export const {
  setKeyPair,
  setSignedPreKey,
  setPreKeys,
  addSessionKey,
  removeSessionKey,
  updateKeyRotationInterval,
  clearError,
  reset,
} = encryptionSlice.actions

export default encryptionSlice.reducer