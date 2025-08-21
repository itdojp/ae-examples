/**
 * Chat Client - WebSocket client for E2E encrypted chat
 */

import { Message, User, ChatSession } from '../domain/entities.js';
import { ChatService } from '../services/chat-service.js';

export interface ChatClientOptions {
  serverUrl: string;
  userId: string;
  token: string;
}

export interface ChatClientCallbacks {
  onMessage?: (message: Message) => void;
  onTyping?: (userId: string, isTyping: boolean) => void;
  onPresence?: (userId: string, status: string) => void;
  onRead?: (messageId: string, readBy: string) => void;
  onConnectionChange?: (connected: boolean) => void;
  onError?: (error: string) => void;
}

export class ChatClient {
  private ws: WebSocket | null = null;
  private reconnectTimer: NodeJS.Timeout | null = null;
  private reconnectAttempts = 0;
  private maxReconnectAttempts = 5;
  private reconnectDelay = 1000;
  private messageQueue: Message[] = [];
  private isConnected = false;

  constructor(
    private options: ChatClientOptions,
    private callbacks: ChatClientCallbacks,
    private chatService: ChatService
  ) {}

  /**
   * Connect to the WebSocket server
   */
  connect(): void {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      return;
    }

    const wsUrl = `${this.options.serverUrl}/ws`;
    this.ws = new WebSocket(wsUrl);

    this.ws.onopen = () => {
      console.log('WebSocket connected');
      this.isConnected = true;
      this.reconnectAttempts = 0;
      
      // Authenticate
      this.send({
        type: 'auth',
        payload: {
          userId: this.options.userId,
          token: this.options.token
        },
        id: this.generateId()
      });

      // Send queued messages
      this.flushMessageQueue();
      
      this.callbacks.onConnectionChange?.(true);
    };

    this.ws.onmessage = async (event) => {
      try {
        const message = JSON.parse(event.data);
        await this.handleMessage(message);
      } catch (error) {
        console.error('Error parsing message:', error);
      }
    };

    this.ws.onclose = () => {
      console.log('WebSocket disconnected');
      this.isConnected = false;
      this.callbacks.onConnectionChange?.(false);
      this.attemptReconnect();
    };

    this.ws.onerror = (error) => {
      console.error('WebSocket error:', error);
      this.callbacks.onError?.('Connection error');
    };
  }

  /**
   * Disconnect from the server
   */
  disconnect(): void {
    if (this.reconnectTimer) {
      clearTimeout(this.reconnectTimer);
      this.reconnectTimer = null;
    }
    
    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }
    
    this.isConnected = false;
    this.callbacks.onConnectionChange?.(false);
  }

  /**
   * Send an encrypted message
   */
  async sendMessage(sessionId: string, content: string): Promise<void> {
    const messageContent = {
      getText: () => content,
      getMentions: () => [],
      getAttachments: () => []
    };

    const message = await this.chatService.sendMessage(sessionId, messageContent as any);
    
    if (this.isConnected) {
      this.send({
        type: 'message',
        payload: {
          sessionId,
          message
        },
        id: this.generateId()
      });
    } else {
      // Queue message for later
      this.messageQueue.push(message);
    }
  }

  /**
   * Send typing indicator
   */
  sendTyping(recipientId: string, isTyping: boolean): void {
    if (!this.isConnected) return;
    
    this.send({
      type: 'typing',
      payload: {
        recipientId,
        isTyping
      },
      id: this.generateId()
    });
  }

  /**
   * Send read receipt
   */
  sendReadReceipt(messageId: string, senderId: string): void {
    if (!this.isConnected) return;
    
    this.send({
      type: 'read',
      payload: {
        messageId,
        senderId
      },
      id: this.generateId()
    });
  }

  /**
   * Update presence status
   */
  updatePresence(status: 'online' | 'away' | 'offline'): void {
    if (!this.isConnected) return;
    
    this.send({
      type: 'presence',
      payload: {
        status
      },
      id: this.generateId()
    });
  }

  /**
   * Handle incoming WebSocket message
   */
  private async handleMessage(message: any): Promise<void> {
    switch (message.type) {
      case 'auth':
        if (message.payload.success) {
          console.log('Authentication successful');
        } else {
          this.callbacks.onError?.('Authentication failed');
          this.disconnect();
        }
        break;
      
      case 'message':
        // Decrypt message using chat service
        const decrypted = await this.chatService.receiveMessage(
          message.payload.sessionId,
          message.payload.message
        );
        
        // Update message with decrypted content
        const decryptedMessage = {
          ...message.payload.message,
          content: decrypted
        };
        
        this.callbacks.onMessage?.(decryptedMessage);
        break;
      
      case 'message_ack':
        console.log(`Message ${message.payload.messageId} status: ${message.payload.status}`);
        break;
      
      case 'typing':
        this.callbacks.onTyping?.(
          message.payload.userId,
          message.payload.isTyping
        );
        break;
      
      case 'read':
        this.callbacks.onRead?.(
          message.payload.messageId,
          message.payload.readBy
        );
        break;
      
      case 'presence':
        this.callbacks.onPresence?.(
          message.payload.userId,
          message.payload.status
        );
        break;
      
      case 'key_exchange':
        // Handle key exchange for session establishment
        console.log('Key exchange from:', message.payload.senderId);
        break;
      
      case 'error':
        this.callbacks.onError?.(message.payload.error);
        break;
      
      default:
        console.warn('Unknown message type:', message.type);
    }
  }

  /**
   * Send a message through WebSocket
   */
  private send(message: any): void {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(message));
    }
  }

  /**
   * Attempt to reconnect to the server
   */
  private attemptReconnect(): void {
    if (this.reconnectAttempts >= this.maxReconnectAttempts) {
      this.callbacks.onError?.('Max reconnection attempts reached');
      return;
    }

    this.reconnectAttempts++;
    const delay = this.reconnectDelay * Math.pow(2, this.reconnectAttempts - 1);
    
    console.log(`Reconnecting in ${delay}ms (attempt ${this.reconnectAttempts})`);
    
    this.reconnectTimer = setTimeout(() => {
      this.connect();
    }, delay);
  }

  /**
   * Send queued messages after reconnection
   */
  private flushMessageQueue(): void {
    while (this.messageQueue.length > 0) {
      const message = this.messageQueue.shift()!;
      this.send({
        type: 'message',
        payload: {
          sessionId: message.id, // Would need proper session tracking
          message
        },
        id: this.generateId()
      });
    }
  }

  /**
   * Generate unique message ID
   */
  private generateId(): string {
    return `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }
}