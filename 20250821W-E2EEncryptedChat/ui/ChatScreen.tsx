'use client';

import React, { useState, useRef, useEffect, useCallback } from 'react';
import { Button } from '@ae-framework/ui/components/button';
import { Input } from '@ae-framework/ui/components/input';
import { Dialog } from '@ae-framework/ui/components/dialog';
import { 
  Send, 
  Shield, 
  ShieldCheck, 
  ShieldAlert,
  Wifi,
  WifiOff,
  Phone,
  Video,
  MoreVertical,
  Info,
  Settings
} from 'lucide-react';

// Types
interface ChatUser {
  id: string;
  name: string;
  avatar?: string;
  isOnline: boolean;
  lastSeen?: Date;
  publicKey?: string;
  isVerified: boolean;
}

interface ChatMessage {
  id: string;
  content: string;
  senderId: string;
  timestamp: Date;
  isEncrypted: boolean;
  status: 'sending' | 'sent' | 'delivered' | 'read';
  isOwn: boolean;
}

interface ChatScreenProps {
  chatId: string;
  currentUser: ChatUser;
  otherUser: ChatUser;
  messages: ChatMessage[];
  isOnline: boolean;
  isE2EEnabled: boolean;
  onSendMessage: (content: string) => Promise<void>;
  onVerifyUser: () => void;
  onCall?: () => void;
  onVideoCall?: () => void;
  typingUsers?: string[];
  className?: string;
}

interface EncryptionStatusProps {
  isE2EEnabled: boolean;
  isVerified: boolean;
  onVerify: () => void;
}

// Encryption Status Indicator Component
const EncryptionStatusIndicator: React.FC<EncryptionStatusProps> = ({
  isE2EEnabled,
  isVerified,
  onVerify
}) => {
  if (!isE2EEnabled) {
    return (
      <div className="flex items-center gap-2 px-3 py-1 bg-gray-100 rounded-full">
        <Shield className="w-4 h-4 text-gray-500" aria-hidden="true" />
        <span className="text-xs text-gray-600">Not encrypted</span>
      </div>
    );
  }

  if (!isVerified) {
    return (
      <button
        onClick={onVerify}
        className="flex items-center gap-2 px-3 py-1 bg-yellow-100 hover:bg-yellow-200 rounded-full transition-colors focus:outline-none focus:ring-2 focus:ring-yellow-500 focus:ring-offset-2"
        aria-label="End-to-end encrypted, click to verify"
      >
        <ShieldAlert className="w-4 h-4 text-yellow-600" aria-hidden="true" />
        <span className="text-xs text-yellow-700">Encrypted - Unverified</span>
      </button>
    );
  }

  return (
    <div className="flex items-center gap-2 px-3 py-1 bg-green-100 rounded-full">
      <ShieldCheck className="w-4 h-4 text-green-600" aria-hidden="true" />
      <span className="text-xs text-green-700">Encrypted & Verified</span>
    </div>
  );
};

// Online Status Component
const OnlineStatus: React.FC<{ isOnline: boolean; lastSeen?: Date }> = ({ 
  isOnline, 
  lastSeen 
}) => {
  const formatLastSeen = (date: Date) => {
    const now = new Date();
    const diff = now.getTime() - date.getTime();
    const minutes = Math.floor(diff / 60000);
    const hours = Math.floor(diff / 3600000);
    const days = Math.floor(diff / 86400000);

    if (minutes < 1) return 'Just now';
    if (minutes < 60) return `${minutes}m ago`;
    if (hours < 24) return `${hours}h ago`;
    if (days < 7) return `${days}d ago`;
    return date.toLocaleDateString();
  };

  return (
    <div className="flex items-center gap-2 text-sm text-gray-500">
      {isOnline ? (
        <>
          <div className="w-2 h-2 bg-green-500 rounded-full" aria-hidden="true" />
          <span>Online</span>
        </>
      ) : (
        <>
          <div className="w-2 h-2 bg-gray-400 rounded-full" aria-hidden="true" />
          <span>
            {lastSeen ? `Last seen ${formatLastSeen(lastSeen)}` : 'Offline'}
          </span>
        </>
      )}
    </div>
  );
};

// Typing Indicator Component
const TypingIndicator: React.FC<{ users: string[] }> = ({ users }) => {
  if (users.length === 0) return null;

  return (
    <div className="flex items-center gap-2 px-4 py-2 text-sm text-gray-500">
      <div className="flex gap-1">
        <div className="w-2 h-2 bg-gray-400 rounded-full animate-bounce" style={{ animationDelay: '0ms' }} />
        <div className="w-2 h-2 bg-gray-400 rounded-full animate-bounce" style={{ animationDelay: '150ms' }} />
        <div className="w-2 h-2 bg-gray-400 rounded-full animate-bounce" style={{ animationDelay: '300ms' }} />
      </div>
      <span>
        {users.length === 1
          ? `${users[0]} is typing...`
          : `${users.length} people are typing...`
        }
      </span>
    </div>
  );
};

// Chat Header Component
const ChatHeader: React.FC<{
  user: ChatUser;
  isOnline: boolean;
  isE2EEnabled: boolean;
  onVerify: () => void;
  onCall?: () => void;
  onVideoCall?: () => void;
}> = ({ user, isOnline, isE2EEnabled, onVerify, onCall, onVideoCall }) => {
  return (
    <div className="flex items-center justify-between p-4 border-b border-gray-200 bg-white">
      <div className="flex items-center gap-3">
        <div className="relative">
          <div className="w-10 h-10 bg-gradient-to-br from-blue-500 to-purple-600 rounded-full flex items-center justify-center text-white font-semibold">
            {user.avatar ? (
              <img
                src={user.avatar}
                alt={`${user.name}'s avatar`}
                className="w-full h-full rounded-full object-cover"
              />
            ) : (
              user.name.charAt(0).toUpperCase()
            )}
          </div>
          <div 
            className={`absolute -bottom-1 -right-1 w-3 h-3 rounded-full border-2 border-white ${
              user.isOnline ? 'bg-green-500' : 'bg-gray-400'
            }`}
            aria-hidden="true"
          />
        </div>
        
        <div className="flex flex-col">
          <h1 className="font-semibold text-gray-900">{user.name}</h1>
          <OnlineStatus isOnline={user.isOnline} lastSeen={user.lastSeen} />
        </div>
      </div>

      <div className="flex items-center gap-2">
        <EncryptionStatusIndicator
          isE2EEnabled={isE2EEnabled}
          isVerified={user.isVerified}
          onVerify={onVerify}
        />
        
        <div className="flex items-center gap-1">
          {onCall && (
            <Button
              variant="ghost"
              size="icon"
              onClick={onCall}
              aria-label="Voice call"
            >
              <Phone className="w-5 h-5" />
            </Button>
          )}
          
          {onVideoCall && (
            <Button
              variant="ghost"
              size="icon"
              onClick={onVideoCall}
              aria-label="Video call"
            >
              <Video className="w-5 h-5" />
            </Button>
          )}
          
          <Button
            variant="ghost"
            size="icon"
            aria-label="More options"
          >
            <MoreVertical className="w-5 h-5" />
          </Button>
        </div>
      </div>
    </div>
  );
};

// Message Input Component
const MessageInput: React.FC<{
  onSendMessage: (content: string) => Promise<void>;
  disabled?: boolean;
  placeholder?: string;
}> = ({ onSendMessage, disabled = false, placeholder = "Type a message..." }) => {
  const [message, setMessage] = useState('');
  const [isLoading, setIsLoading] = useState(false);
  const inputRef = useRef<HTMLInputElement>(null);

  const handleSubmit = useCallback(async (e: React.FormEvent) => {
    e.preventDefault();
    
    if (!message.trim() || isLoading || disabled) return;
    
    const messageContent = message.trim();
    setMessage('');
    setIsLoading(true);
    
    try {
      await onSendMessage(messageContent);
    } catch (error) {
      console.error('Failed to send message:', error);
      setMessage(messageContent); // Restore message on error
    } finally {
      setIsLoading(false);
      inputRef.current?.focus();
    }
  }, [message, isLoading, disabled, onSendMessage]);

  const handleKeyPress = useCallback((e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSubmit(e as any);
    }
  }, [handleSubmit]);

  return (
    <div className="p-4 border-t border-gray-200 bg-white">
      <form onSubmit={handleSubmit} className="flex items-end gap-3">
        <div className="flex-1">
          <Input
            ref={inputRef}
            value={message}
            onChange={(e) => setMessage(e.target.value)}
            onKeyPress={handleKeyPress}
            placeholder={placeholder}
            disabled={disabled || isLoading}
            className="min-h-[44px] resize-none"
            aria-label="Message input"
          />
        </div>
        
        <Button
          type="submit"
          disabled={!message.trim() || isLoading || disabled}
          className="px-4 py-2 min-h-[44px]"
          aria-label="Send message"
        >
          <Send className="w-5 h-5" />
        </Button>
      </form>
    </div>
  );
};

// Connection Status Component
const ConnectionStatus: React.FC<{ isOnline: boolean }> = ({ isOnline }) => {
  if (isOnline) return null;

  return (
    <div className="flex items-center justify-center gap-2 p-2 bg-red-100 text-red-700 text-sm">
      <WifiOff className="w-4 h-4" aria-hidden="true" />
      <span>Connection lost. Trying to reconnect...</span>
    </div>
  );
};

// Main ChatScreen Component
export const ChatScreen: React.FC<ChatScreenProps> = ({
  chatId,
  currentUser,
  otherUser,
  messages,
  isOnline,
  isE2EEnabled,
  onSendMessage,
  onVerifyUser,
  onCall,
  onVideoCall,
  typingUsers = [],
  className = ''
}) => {
  const messagesEndRef = useRef<HTMLDivElement>(null);

  const scrollToBottom = useCallback(() => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  }, []);

  useEffect(() => {
    scrollToBottom();
  }, [messages, scrollToBottom]);

  return (
    <div className={`flex flex-col h-full bg-gray-50 ${className}`}>
      <ConnectionStatus isOnline={isOnline} />
      
      <ChatHeader
        user={otherUser}
        isOnline={isOnline}
        isE2EEnabled={isE2EEnabled}
        onVerify={onVerifyUser}
        onCall={onCall}
        onVideoCall={onVideoCall}
      />

      <div 
        className="flex-1 overflow-y-auto px-4 py-6 space-y-4"
        role="log"
        aria-live="polite"
        aria-label="Chat messages"
      >
        {messages.length === 0 ? (
          <div className="flex flex-col items-center justify-center h-full text-gray-500">
            <div className="w-16 h-16 bg-gray-200 rounded-full flex items-center justify-center mb-4">
              <Shield className="w-8 h-8" />
            </div>
            <h3 className="text-lg font-medium mb-2">
              {isE2EEnabled ? 'Secure conversation started' : 'Start a conversation'}
            </h3>
            <p className="text-center max-w-md">
              {isE2EEnabled
                ? 'Messages are end-to-end encrypted. Only you and the recipient can read them.'
                : 'Send your first message to start the conversation.'
              }
            </p>
          </div>
        ) : (
          <>
            {messages.map((message) => (
              <div
                key={message.id}
                className={`flex ${message.isOwn ? 'justify-end' : 'justify-start'}`}
              >
                <div
                  className={`max-w-xs lg:max-w-md px-4 py-2 rounded-lg ${
                    message.isOwn
                      ? 'bg-blue-500 text-white'
                      : 'bg-white border border-gray-200'
                  }`}
                >
                  <p className="text-sm break-words">{message.content}</p>
                  <div className={`flex items-center justify-between gap-2 mt-1 text-xs ${
                    message.isOwn ? 'text-blue-100' : 'text-gray-500'
                  }`}>
                    <span>{message.timestamp.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })}</span>
                    <div className="flex items-center gap-1">
                      {message.isEncrypted && (
                        <Shield className="w-3 h-3" aria-label="Encrypted message" />
                      )}
                      {message.isOwn && (
                        <span className="capitalize" aria-label={`Message ${message.status}`}>
                          {message.status === 'read' ? '✓✓' : 
                           message.status === 'delivered' ? '✓' : 
                           message.status === 'sending' ? '○' : '✓'}
                        </span>
                      )}
                    </div>
                  </div>
                </div>
              </div>
            ))}
            
            <TypingIndicator users={typingUsers} />
            <div ref={messagesEndRef} aria-hidden="true" />
          </>
        )}
      </div>

      <MessageInput
        onSendMessage={onSendMessage}
        disabled={!isOnline}
        placeholder={isOnline ? "Type a message..." : "Reconnecting..."}
      />
    </div>
  );
};

export default ChatScreen;