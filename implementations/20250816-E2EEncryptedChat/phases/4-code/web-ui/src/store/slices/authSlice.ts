import { createSlice, createAsyncThunk, PayloadAction } from '@reduxjs/toolkit'
// Use mock service for development
import { mockAuthService as authService } from '../../services/mockAPI'

export interface User {
  id: string
  email: string
  displayName: string
  publicKey: string
  createdAt: string
}

export interface AuthState {
  user: User | null
  token: string | null
  refreshToken: string | null
  isAuthenticated: boolean
  isLoading: boolean
  error: string | null
  deviceId: string | null
  twoFactorEnabled: boolean
}

export interface LoginCredentials {
  email: string
  password: string
  totpCode?: string
  deviceId: string
}

export interface RegisterData {
  email: string
  password: string
  displayName: string
  publicKey: string
}

const initialState: AuthState = {
  user: null,
  token: null,
  refreshToken: null,
  isAuthenticated: false,
  isLoading: false,
  error: null,
  deviceId: null,
  twoFactorEnabled: false,
}

// Async Thunks
export const login = createAsyncThunk(
  'auth/login',
  async (credentials: LoginCredentials, { rejectWithValue }) => {
    try {
      const response = await authService.login(credentials)
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Login failed')
    }
  }
)

export const register = createAsyncThunk(
  'auth/register',
  async (userData: RegisterData, { rejectWithValue }) => {
    try {
      const response = await authService.register(userData)
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Registration failed')
    }
  }
)

export const logout = createAsyncThunk(
  'auth/logout',
  async (_, { getState, rejectWithValue }) => {
    try {
      const state = getState() as { auth: AuthState }
      if (state.auth.token) {
        await authService.logout(state.auth.token)
      }
    } catch (error) {
      // Continue with logout even if API call fails
    }
  }
)

export const refreshAuth = createAsyncThunk(
  'auth/refresh',
  async (_, { getState, rejectWithValue }) => {
    try {
      const state = getState() as { auth: AuthState }
      if (!state.auth.refreshToken) {
        throw new Error('No refresh token available')
      }
      const response = await authService.refreshToken(state.auth.refreshToken)
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Token refresh failed')
    }
  }
)

const authSlice = createSlice({
  name: 'auth',
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null
    },
    setDeviceId: (state, action: PayloadAction<string>) => {
      state.deviceId = action.payload
    },
    loadFromStorage: (state) => {
      const token = localStorage.getItem('auth_token')
      const refreshToken = localStorage.getItem('refresh_token')
      const user = localStorage.getItem('user')
      
      if (token && refreshToken && user) {
        state.token = token
        state.refreshToken = refreshToken
        state.user = JSON.parse(user)
        state.isAuthenticated = true
      }
    },
  },
  extraReducers: (builder) => {
    builder
      // Login
      .addCase(login.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(login.fulfilled, (state, action) => {
        state.isLoading = false
        state.user = action.payload.user
        state.token = action.payload.token
        state.refreshToken = action.payload.refreshToken
        state.isAuthenticated = true
        state.twoFactorEnabled = action.payload.user.twoFactorEnabled
        
        // Store in localStorage
        localStorage.setItem('auth_token', action.payload.token)
        localStorage.setItem('refresh_token', action.payload.refreshToken)
        localStorage.setItem('user', JSON.stringify(action.payload.user))
      })
      .addCase(login.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Register
      .addCase(register.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(register.fulfilled, (state, action) => {
        state.isLoading = false
        state.user = action.payload.user
        state.token = action.payload.token
        state.refreshToken = action.payload.refreshToken
        state.isAuthenticated = true
        
        // Store in localStorage
        localStorage.setItem('auth_token', action.payload.token)
        localStorage.setItem('refresh_token', action.payload.refreshToken)
        localStorage.setItem('user', JSON.stringify(action.payload.user))
      })
      .addCase(register.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Logout
      .addCase(logout.fulfilled, (state) => {
        state.user = null
        state.token = null
        state.refreshToken = null
        state.isAuthenticated = false
        state.twoFactorEnabled = false
        
        // Clear localStorage
        localStorage.removeItem('auth_token')
        localStorage.removeItem('refresh_token')
        localStorage.removeItem('user')
      })
      
      // Refresh
      .addCase(refreshAuth.fulfilled, (state, action) => {
        state.token = action.payload.token
        state.refreshToken = action.payload.refreshToken
        localStorage.setItem('auth_token', action.payload.token)
        localStorage.setItem('refresh_token', action.payload.refreshToken)
      })
      .addCase(refreshAuth.rejected, (state) => {
        // Token refresh failed, logout user
        state.user = null
        state.token = null
        state.refreshToken = null
        state.isAuthenticated = false
        localStorage.clear()
      })
  },
})

export const { clearError, setDeviceId, loadFromStorage } = authSlice.actions
export default authSlice.reducer