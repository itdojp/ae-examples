import { createSlice, createAsyncThunk, PayloadAction } from '@reduxjs/toolkit'
// Use mock service for development
import { mockChatService as chatService } from '../../services/mockAPI'

export interface Message {
  id: string
  conversationId: string
  senderId: string
  recipientId: string
  encryptedContent: ArrayBuffer
  signature: ArrayBuffer
  nonce: ArrayBuffer
  timestamp: number
  deliveryStatus: 'sent' | 'delivered' | 'read'
  messageType: 'text' | 'image' | 'file'
}

export interface Conversation {
  id: string
  participantIds: string[]
  name?: string
  isGroup: boolean
  lastMessage?: Message
  lastActivity: number
  unreadCount: number
  encryptionStatus: 'secure' | 'pending' | 'failed'
}

export interface Contact {
  id: string
  displayName: string
  email: string
  publicKey: string
  verificationStatus: 'verified' | 'unverified' | 'pending'
  safetyNumber: string
  lastSeen?: number
  isOnline: boolean
}

export interface ChatState {
  conversations: Conversation[]
  messages: { [conversationId: string]: Message[] }
  contacts: Contact[]
  activeConversationId: string | null
  isConnected: boolean
  isLoading: boolean
  error: string | null
  typingUsers: { [conversationId: string]: string[] }
}

const initialState: ChatState = {
  conversations: [],
  messages: {},
  contacts: [],
  activeConversationId: null,
  isConnected: false,
  isLoading: false,
  error: null,
  typingUsers: {},
}

// Async Thunks
export const loadConversations = createAsyncThunk(
  'chat/loadConversations',
  async (_, { rejectWithValue }) => {
    try {
      const response = await chatService.getConversations()
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Failed to load conversations')
    }
  }
)

export const loadMessages = createAsyncThunk(
  'chat/loadMessages',
  async (conversationId: string, { rejectWithValue }) => {
    try {
      const response = await chatService.getMessages(conversationId)
      return { conversationId, messages: response.data }
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Failed to load messages')
    }
  }
)

export const sendMessage = createAsyncThunk(
  'chat/sendMessage',
  async (
    { conversationId, content, recipientId }: 
    { conversationId: string; content: string; recipientId: string },
    { rejectWithValue }
  ) => {
    try {
      const response = await chatService.sendMessage({
        conversationId,
        content,
        recipientId,
      })
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Failed to send message')
    }
  }
)

export const loadContacts = createAsyncThunk(
  'chat/loadContacts',
  async (_, { rejectWithValue }) => {
    try {
      const response = await chatService.getContacts()
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Failed to load contacts')
    }
  }
)

export const addContact = createAsyncThunk(
  'chat/addContact',
  async (email: string, { rejectWithValue }) => {
    try {
      const response = await chatService.addContact(email)
      return response.data
    } catch (error: any) {
      return rejectWithValue(error.response?.data?.message || 'Failed to add contact')
    }
  }
)

const chatSlice = createSlice({
  name: 'chat',
  initialState,
  reducers: {
    setActiveConversation: (state, action: PayloadAction<string | null>) => {
      state.activeConversationId = action.payload
      
      // Mark messages as read
      if (action.payload && state.messages[action.payload]) {
        const conversation = state.conversations.find(c => c.id === action.payload)
        if (conversation) {
          conversation.unreadCount = 0
        }
      }
    },
    
    addMessage: (state, action: PayloadAction<Message>) => {
      const message = action.payload
      const conversationId = message.conversationId
      
      if (!state.messages[conversationId]) {
        state.messages[conversationId] = []
      }
      
      state.messages[conversationId].push(message)
      
      // Update conversation last message and activity
      const conversation = state.conversations.find(c => c.id === conversationId)
      if (conversation) {
        conversation.lastMessage = message
        conversation.lastActivity = message.timestamp
        
        // Increment unread count if not active conversation
        if (state.activeConversationId !== conversationId) {
          conversation.unreadCount += 1
        }
      }
    },
    
    updateMessageStatus: (state, action: PayloadAction<{
      messageId: string
      conversationId: string
      status: 'sent' | 'delivered' | 'read'
    }>) => {
      const { messageId, conversationId, status } = action.payload
      const messages = state.messages[conversationId]
      
      if (messages) {
        const message = messages.find(m => m.id === messageId)
        if (message) {
          message.deliveryStatus = status
        }
      }
    },
    
    setTypingUsers: (state, action: PayloadAction<{
      conversationId: string
      userIds: string[]
    }>) => {
      const { conversationId, userIds } = action.payload
      state.typingUsers[conversationId] = userIds
    },
    
    setConnectionStatus: (state, action: PayloadAction<boolean>) => {
      state.isConnected = action.payload
    },
    
    updateContactOnlineStatus: (state, action: PayloadAction<{
      contactId: string
      isOnline: boolean
      lastSeen?: number
    }>) => {
      const { contactId, isOnline, lastSeen } = action.payload
      const contact = state.contacts.find(c => c.id === contactId)
      
      if (contact) {
        contact.isOnline = isOnline
        if (lastSeen) {
          contact.lastSeen = lastSeen
        }
      }
    },
    
    clearError: (state) => {
      state.error = null
    },
  },
  extraReducers: (builder) => {
    builder
      // Load Conversations
      .addCase(loadConversations.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(loadConversations.fulfilled, (state, action) => {
        state.isLoading = false
        state.conversations = action.payload
      })
      .addCase(loadConversations.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Load Messages
      .addCase(loadMessages.pending, (state) => {
        state.isLoading = true
        state.error = null
      })
      .addCase(loadMessages.fulfilled, (state, action) => {
        state.isLoading = false
        const { conversationId, messages } = action.payload
        state.messages[conversationId] = messages
      })
      .addCase(loadMessages.rejected, (state, action) => {
        state.isLoading = false
        state.error = action.payload as string
      })
      
      // Send Message
      .addCase(sendMessage.pending, (state) => {
        state.error = null
      })
      .addCase(sendMessage.fulfilled, (state, action) => {
        // Message will be added via WebSocket event
        // This just confirms successful sending
      })
      .addCase(sendMessage.rejected, (state, action) => {
        state.error = action.payload as string
      })
      
      // Load Contacts
      .addCase(loadContacts.fulfilled, (state, action) => {
        state.contacts = action.payload
      })
      .addCase(loadContacts.rejected, (state, action) => {
        state.error = action.payload as string
      })
      
      // Add Contact
      .addCase(addContact.fulfilled, (state, action) => {
        state.contacts.push(action.payload)
      })
      .addCase(addContact.rejected, (state, action) => {
        state.error = action.payload as string
      })
  },
})

export const {
  setActiveConversation,
  addMessage,
  updateMessageStatus,
  setTypingUsers,
  setConnectionStatus,
  updateContactOnlineStatus,
  clearError,
} = chatSlice.actions

export default chatSlice.reducer