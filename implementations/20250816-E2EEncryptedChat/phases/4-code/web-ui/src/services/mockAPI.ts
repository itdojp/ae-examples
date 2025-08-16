// Mock API for development testing
import { LoginCredentials, RegisterData } from '../store/slices/authSlice'

// Simulate API delay
const delay = (ms: number) => new Promise(resolve => setTimeout(resolve, ms))

// Mock user data
const mockUsers = [
  {
    id: '1',
    email: 'test@example.com',
    displayName: 'Test User',
    publicKey: 'mock-public-key-123',
    createdAt: new Date().toISOString(),
    twoFactorEnabled: false,
  }
]

export const mockAuthService = {
  login: async (credentials: LoginCredentials) => {
    await delay(1000)
    
    if (credentials.email === 'test@example.com' && credentials.password === 'password123!') {
      return {
        data: {
          user: mockUsers[0],
          token: 'mock-jwt-token-' + Date.now(),
          refreshToken: 'mock-refresh-token-' + Date.now(),
        }
      }
    } else {
      throw new Error('Invalid credentials')
    }
  },
  
  register: async (userData: RegisterData) => {
    await delay(1500)
    
    const newUser = {
      id: Date.now().toString(),
      email: userData.email,
      displayName: userData.displayName,
      publicKey: userData.publicKey,
      createdAt: new Date().toISOString(),
      twoFactorEnabled: false,
    }
    
    mockUsers.push(newUser)
    
    return {
      data: {
        user: newUser,
        token: 'mock-jwt-token-' + Date.now(),
        refreshToken: 'mock-refresh-token-' + Date.now(),
      }
    }
  },
  
  logout: async (token: string) => {
    await delay(500)
    return { data: { success: true } }
  },
  
  refreshToken: async (refreshToken: string) => {
    await delay(500)
    return {
      data: {
        token: 'mock-jwt-token-refreshed-' + Date.now(),
        refreshToken: 'mock-refresh-token-refreshed-' + Date.now(),
      }
    }
  }
}

export const mockChatService = {
  getConversations: async () => {
    await delay(800)
    return {
      data: [
        {
          id: '1',
          participantIds: ['1', '2'],
          name: 'Test Conversation',
          isGroup: false,
          lastActivity: Date.now(),
          unreadCount: 0,
          encryptionStatus: 'secure',
        }
      ]
    }
  },
  
  getMessages: async (conversationId: string) => {
    await delay(600)
    return {
      data: [
        {
          id: '1',
          conversationId,
          senderId: '1',
          recipientId: '2',
          encryptedContent: new ArrayBuffer(0),
          signature: new ArrayBuffer(0),
          nonce: new ArrayBuffer(0),
          timestamp: Date.now() - 60000,
          deliveryStatus: 'read',
          messageType: 'text',
        }
      ]
    }
  },
  
  sendMessage: async (messageData: any) => {
    await delay(400)
    return {
      data: {
        id: Date.now().toString(),
        ...messageData,
        timestamp: Date.now(),
        deliveryStatus: 'sent',
      }
    }
  },
  
  getContacts: async () => {
    await delay(500)
    return {
      data: [
        {
          id: '2',
          displayName: 'Alice Smith',
          email: 'alice@example.com',
          publicKey: 'alice-public-key-456',
          verificationStatus: 'verified',
          safetyNumber: '12345 67890 12345 67890 12345',
          isOnline: true,
        },
        {
          id: '3',
          displayName: 'Bob Johnson',
          email: 'bob@example.com',
          publicKey: 'bob-public-key-789',
          verificationStatus: 'verified',
          safetyNumber: '54321 09876 54321 09876 54321',
          isOnline: false,
        },
        {
          id: '4',
          displayName: 'Carol Davis',
          email: 'carol@example.com',
          publicKey: 'carol-public-key-012',
          verificationStatus: 'unverified',
          safetyNumber: '11111 22222 33333 44444 55555',
          isOnline: true,
        }
      ]
    }
  },
  
  addContact: async (email: string) => {
    await delay(700)
    return {
      data: {
        id: Date.now().toString(),
        displayName: email.split('@')[0],
        email,
        publicKey: 'generated-public-key-' + Date.now(),
        verificationStatus: 'unverified',
        safetyNumber: '00000 00000 00000 00000 00000',
        isOnline: false,
      }
    }
  }
}