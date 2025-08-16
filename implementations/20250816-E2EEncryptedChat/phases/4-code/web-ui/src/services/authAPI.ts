import axios from 'axios'
import { LoginCredentials, RegisterData } from '../store/slices/authSlice'

const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || 'http://localhost:5000/api'

const authAPI = axios.create({
  baseURL: `${API_BASE_URL}/auth`,
  headers: {
    'Content-Type': 'application/json',
  },
})

// Request interceptor to add auth token
authAPI.interceptors.request.use((config) => {
  const token = localStorage.getItem('auth_token')
  if (token) {
    config.headers.Authorization = `Bearer ${token}`
  }
  return config
})

// Response interceptor to handle token refresh
authAPI.interceptors.response.use(
  (response) => response,
  async (error) => {
    const originalRequest = error.config
    
    if (error.response?.status === 401 && !originalRequest._retry) {
      originalRequest._retry = true
      
      const refreshToken = localStorage.getItem('refresh_token')
      if (refreshToken) {
        try {
          const response = await authAPI.post('/refresh', { refreshToken })
          const { token } = response.data
          
          localStorage.setItem('auth_token', token)
          originalRequest.headers.Authorization = `Bearer ${token}`
          
          return authAPI(originalRequest)
        } catch (refreshError) {
          // Refresh failed, redirect to login
          localStorage.clear()
          window.location.href = '/login'
        }
      }
    }
    
    return Promise.reject(error)
  }
)

const authService = {
  login: (credentials: LoginCredentials) => 
    authAPI.post('/login', credentials),
    
  register: (userData: RegisterData) => 
    authAPI.post('/register', userData),
    
  logout: (token: string) => 
    authAPI.post('/logout', {}, {
      headers: { Authorization: `Bearer ${token}` }
    }),
    
  refreshToken: (refreshToken: string) => 
    authAPI.post('/refresh', { refreshToken }),
    
  verifyEmail: (token: string) => 
    authAPI.post('/verify-email', { token }),
    
  requestPasswordReset: (email: string) => 
    authAPI.post('/request-password-reset', { email }),
    
  resetPassword: (token: string, newPassword: string) => 
    authAPI.post('/reset-password', { token, newPassword }),
    
  enableTwoFactor: () => 
    authAPI.post('/2fa/enable'),
    
  verifyTwoFactor: (token: string) => 
    authAPI.post('/2fa/verify', { token }),
    
  disableTwoFactor: (token: string) => 
    authAPI.post('/2fa/disable', { token }),
    
  getProfile: () => 
    authAPI.get('/profile'),
    
  updateProfile: (updates: Partial<{
    displayName: string
    email: string
    avatar: string
  }>) => 
    authAPI.patch('/profile', updates),
    
  changePassword: (currentPassword: string, newPassword: string) => 
    authAPI.post('/change-password', { currentPassword, newPassword }),
    
  deleteAccount: (password: string) => 
    authAPI.delete('/account', { data: { password } }),
    
  // Device management
  getDevices: () => 
    authAPI.get('/devices'),
    
  registerDevice: (deviceInfo: {
    name: string
    type: string
    fingerprint: string
  }) => 
    authAPI.post('/devices', deviceInfo),
    
  removeDevice: (deviceId: string) => 
    authAPI.delete(`/devices/${deviceId}`),
    
  trustDevice: (deviceId: string) => 
    authAPI.post(`/devices/${deviceId}/trust`),
}

export { authAPI, authService }