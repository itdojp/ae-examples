import axios from 'axios'

const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || 'http://localhost:5000/api'

const chatAPI = axios.create({
  baseURL: API_BASE_URL,
  headers: {
    'Content-Type': 'application/json',
  },
})

// Request interceptor to add auth token
chatAPI.interceptors.request.use((config) => {
  const token = localStorage.getItem('auth_token')
  if (token) {
    config.headers.Authorization = `Bearer ${token}`
  }
  return config
})

const chatService = {
  // Conversations
  getConversations: () => 
    chatAPI.get('/conversations'),
    
  createConversation: (participantIds: string[], name?: string) => 
    chatAPI.post('/conversations', { participantIds, name }),
    
  getConversation: (conversationId: string) => 
    chatAPI.get(`/conversations/${conversationId}`),
    
  updateConversation: (conversationId: string, updates: {
    name?: string
    settings?: any
  }) => 
    chatAPI.patch(`/conversations/${conversationId}`, updates),
    
  deleteConversation: (conversationId: string) => 
    chatAPI.delete(`/conversations/${conversationId}`),
    
  // Messages
  getMessages: (conversationId: string, limit = 50, before?: string) => 
    chatAPI.get(`/conversations/${conversationId}/messages`, {
      params: { limit, before }
    }),
    
  sendMessage: (messageData: {
    conversationId: string
    content: string
    recipientId: string
    messageType?: 'text' | 'image' | 'file'
  }) => 
    chatAPI.post('/messages', messageData),
    
  getMessage: (messageId: string) => 
    chatAPI.get(`/messages/${messageId}`),
    
  deleteMessage: (messageId: string, forEveryone = false) => 
    chatAPI.delete(`/messages/${messageId}`, {
      data: { forEveryone }
    }),
    
  markAsRead: (messageIds: string[]) => 
    chatAPI.post('/messages/mark-read', { messageIds }),
    
  // Contacts
  getContacts: () => 
    chatAPI.get('/contacts'),
    
  addContact: (email: string) => 
    chatAPI.post('/contacts', { email }),
    
  removeContact: (contactId: string) => 
    chatAPI.delete(`/contacts/${contactId}`),
    
  blockContact: (contactId: string) => 
    chatAPI.post(`/contacts/${contactId}/block`),
    
  unblockContact: (contactId: string) => 
    chatAPI.post(`/contacts/${contactId}/unblock`),
    
  searchUsers: (query: string) => 
    chatAPI.get(`/users/search`, { params: { q: query } }),
    
  // Key Management
  getKeyBundle: (userId: string) => 
    chatAPI.get(`/users/${userId}/keys`),
    
  uploadPreKeys: (preKeys: any[]) => 
    chatAPI.post('/keys/prekeys', { preKeys }),
    
  uploadSignedPreKey: (signedPreKey: any) => 
    chatAPI.post('/keys/signed-prekey', signedPreKey),
    
  getPreKey: (userId: string) => 
    chatAPI.get(`/users/${userId}/prekey`),
    
  // File Upload
  uploadFile: (file: File, conversationId: string) => {
    const formData = new FormData()
    formData.append('file', file)
    formData.append('conversationId', conversationId)
    
    return chatAPI.post('/files/upload', formData, {
      headers: {
        'Content-Type': 'multipart/form-data',
      },
    })
  },
  
  downloadFile: (fileId: string) => 
    chatAPI.get(`/files/${fileId}`, { responseType: 'blob' }),
    
  // Settings
  getSettings: () => 
    chatAPI.get('/settings'),
    
  updateSettings: (settings: any) => 
    chatAPI.patch('/settings', settings),
    
  // Typing indicators
  startTyping: (conversationId: string) => 
    chatAPI.post(`/conversations/${conversationId}/typing/start`),
    
  stopTyping: (conversationId: string) => 
    chatAPI.post(`/conversations/${conversationId}/typing/stop`),
    
  // Presence
  setPresence: (status: 'online' | 'away' | 'offline') => 
    chatAPI.post('/presence', { status }),
    
  getPresence: (userIds: string[]) => 
    chatAPI.post('/presence/batch', { userIds }),
}

export { chatAPI, chatService }