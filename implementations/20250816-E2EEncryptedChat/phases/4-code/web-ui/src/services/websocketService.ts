import { io, Socket } from 'socket.io-client'
import { store } from '../store/store'
import { 
  addMessage, 
  updateMessageStatus, 
  setTypingUsers, 
  setConnectionStatus,
  updateContactOnlineStatus 
} from '../store/slices/chatSlice'

export class WebSocketService {
  private socket: Socket | null = null
  private reconnectAttempts = 0
  private maxReconnectAttempts = 5
  private reconnectInterval = 1000
  private isConnecting = false

  connect(token: string): void {
    if (this.socket || this.isConnecting) {
      return
    }

    this.isConnecting = true
    const wsUrl = import.meta.env.VITE_WS_URL || 'http://localhost:5000'
    
    this.socket = io(wsUrl, {
      auth: {
        token,
      },
      transports: ['websocket'],
      upgrade: false,
      rememberUpgrade: false,
    })

    this.setupEventListeners()
  }

  disconnect(): void {
    if (this.socket) {
      this.socket.disconnect()
      this.socket = null
    }
    this.isConnecting = false
    this.reconnectAttempts = 0
    store.dispatch(setConnectionStatus(false))
  }

  private setupEventListeners(): void {
    if (!this.socket) return

    // Connection events
    this.socket.on('connect', () => {
      console.log('WebSocket connected')
      this.isConnecting = false
      this.reconnectAttempts = 0
      store.dispatch(setConnectionStatus(true))
    })

    this.socket.on('disconnect', (reason) => {
      console.log('WebSocket disconnected:', reason)
      store.dispatch(setConnectionStatus(false))
      
      // Auto-reconnect on certain disconnect reasons
      if (reason === 'io server disconnect') {
        // Server initiated disconnect, don't reconnect automatically
        return
      }
      
      this.scheduleReconnect()
    })

    this.socket.on('connect_error', (error) => {
      console.error('WebSocket connection error:', error)
      this.isConnecting = false
      store.dispatch(setConnectionStatus(false))
      this.scheduleReconnect()
    })

    // Message events
    this.socket.on('new_message', (message) => {
      console.log('Received new message:', message)
      store.dispatch(addMessage(message))
    })

    this.socket.on('message_status_update', ({ messageId, conversationId, status }) => {
      store.dispatch(updateMessageStatus({
        messageId,
        conversationId,
        status,
      }))
    })

    // Typing events
    this.socket.on('typing_start', ({ conversationId, userId }) => {
      const state = store.getState()
      const currentTypingUsers = state.chat.typingUsers[conversationId] || []
      
      if (!currentTypingUsers.includes(userId)) {
        store.dispatch(setTypingUsers({
          conversationId,
          userIds: [...currentTypingUsers, userId],
        }))
      }
    })

    this.socket.on('typing_stop', ({ conversationId, userId }) => {
      const state = store.getState()
      const currentTypingUsers = state.chat.typingUsers[conversationId] || []
      
      store.dispatch(setTypingUsers({
        conversationId,
        userIds: currentTypingUsers.filter(id => id !== userId),
      }))
    })

    // Presence events
    this.socket.on('user_online', ({ userId }) => {
      store.dispatch(updateContactOnlineStatus({
        contactId: userId,
        isOnline: true,
      }))
    })

    this.socket.on('user_offline', ({ userId, lastSeen }) => {
      store.dispatch(updateContactOnlineStatus({
        contactId: userId,
        isOnline: false,
        lastSeen,
      }))
    })

    // Key exchange events
    this.socket.on('key_exchange_request', ({ fromUserId, keyBundle }) => {
      console.log('Received key exchange request from:', fromUserId)
      // Handle key exchange in encryption service
      this.handleKeyExchangeRequest(fromUserId, keyBundle)
    })

    this.socket.on('key_exchange_response', ({ fromUserId, keyBundle }) => {
      console.log('Received key exchange response from:', fromUserId)
      // Handle key exchange response
      this.handleKeyExchangeResponse(fromUserId, keyBundle)
    })

    // Security events
    this.socket.on('security_alert', ({ type, message, timestamp }) => {
      console.warn('Security alert:', { type, message, timestamp })
      // Show security alert to user
      this.showSecurityAlert(type, message)
    })

    // Error events
    this.socket.on('error', (error) => {
      console.error('WebSocket error:', error)
      // Handle specific error types
      if (error.type === 'authentication') {
        // Token expired or invalid
        this.disconnect()
        // Redirect to login
        window.location.href = '/login'
      }
    })
  }

  private scheduleReconnect(): void {
    if (this.reconnectAttempts >= this.maxReconnectAttempts) {
      console.error('Max reconnection attempts reached')
      return
    }

    this.reconnectAttempts++
    const delay = this.reconnectInterval * Math.pow(2, this.reconnectAttempts - 1) // Exponential backoff
    
    console.log(`Scheduling reconnection attempt ${this.reconnectAttempts} in ${delay}ms`)
    
    setTimeout(() => {
      if (!this.socket?.connected) {
        console.log(`Reconnection attempt ${this.reconnectAttempts}`)
        this.socket?.connect()
      }
    }, delay)
  }

  // Message sending methods
  sendMessage(data: {
    conversationId: string
    encryptedContent: ArrayBuffer
    signature: ArrayBuffer
    nonce: ArrayBuffer
    recipientId: string
  }): void {
    if (!this.socket?.connected) {
      throw new Error('WebSocket not connected')
    }

    this.socket.emit('send_message', {
      ...data,
      encryptedContent: Array.from(new Uint8Array(data.encryptedContent)),
      signature: Array.from(new Uint8Array(data.signature)),
      nonce: Array.from(new Uint8Array(data.nonce)),
    })
  }

  // Typing indicators
  startTyping(conversationId: string): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('typing_start', { conversationId })
  }

  stopTyping(conversationId: string): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('typing_stop', { conversationId })
  }

  // Presence
  setPresence(status: 'online' | 'away' | 'offline'): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('set_presence', { status })
  }

  // Key exchange
  sendKeyExchangeRequest(toUserId: string, keyBundle: any): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('key_exchange_request', {
      toUserId,
      keyBundle,
    })
  }

  sendKeyExchangeResponse(toUserId: string, keyBundle: any): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('key_exchange_response', {
      toUserId,
      keyBundle,
    })
  }

  // Join/leave conversation rooms
  joinConversation(conversationId: string): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('join_conversation', { conversationId })
  }

  leaveConversation(conversationId: string): void {
    if (!this.socket?.connected) return
    
    this.socket.emit('leave_conversation', { conversationId })
  }

  private async handleKeyExchangeRequest(fromUserId: string, keyBundle: any): Promise<void> {
    try {
      // Import encryption service
      const { EncryptionService } = await import('./encryptionService')
      const encryptionService = new EncryptionService()
      
      // Create session with the provided key bundle
      // This would trigger the key exchange process
      console.log('Processing key exchange request...')
      
      // For now, just log the event
      // In a real implementation, this would handle the complete key exchange
    } catch (error) {
      console.error('Failed to handle key exchange request:', error)
    }
  }

  private async handleKeyExchangeResponse(fromUserId: string, keyBundle: any): Promise<void> {
    try {
      console.log('Processing key exchange response...')
      // Handle the key exchange response
    } catch (error) {
      console.error('Failed to handle key exchange response:', error)
    }
  }

  private showSecurityAlert(type: string, message: string): void {
    // This would show a security alert to the user
    // For now, just log it
    console.warn(`Security Alert [${type}]: ${message}`)
    
    // In a real implementation, you might dispatch an action to show a notification
    // or modal dialog to inform the user about the security event
  }

  // Utility methods
  isConnected(): boolean {
    return this.socket?.connected || false
  }

  getConnectionStatus(): 'connected' | 'connecting' | 'disconnected' {
    if (this.socket?.connected) return 'connected'
    if (this.isConnecting) return 'connecting'
    return 'disconnected'
  }
}

// Export singleton instance
export const websocketService = new WebSocketService()