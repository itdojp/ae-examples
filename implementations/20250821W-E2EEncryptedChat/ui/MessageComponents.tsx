'use client';

import React, { useMemo } from 'react';
import { 
  Shield, 
  ShieldCheck, 
  Check, 
  CheckCheck,
  Clock,
  AlertCircle,
  Eye,
  Loader2
} from 'lucide-react';

// Types
export interface Message {
  id: string;
  content: string;
  senderId: string;
  timestamp: Date;
  isEncrypted: boolean;
  status: 'sending' | 'sent' | 'delivered' | 'read' | 'failed';
  isOwn: boolean;
  type?: 'text' | 'image' | 'file' | 'system';
  editedAt?: Date;
  replyTo?: string;
}

export interface MessageBubbleProps {
  message: Message;
  showSender?: boolean;
  senderName?: string;
  isGrouped?: boolean;
  onRetry?: (messageId: string) => void;
  className?: string;
}

export interface MessageStatusProps {
  status: Message['status'];
  timestamp: Date;
  isOwn: boolean;
  className?: string;
}

export interface TypingIndicatorProps {
  users: string[];
  className?: string;
}

export interface MessageTimestampProps {
  timestamp: Date;
  editedAt?: Date;
  showDate?: boolean;
  className?: string;
}

export interface EncryptionIndicatorProps {
  isEncrypted: boolean;
  isVerified?: boolean;
  size?: 'sm' | 'md' | 'lg';
  showLabel?: boolean;
  className?: string;
}

// Encryption Indicator Component
export const EncryptionIndicator: React.FC<EncryptionIndicatorProps> = ({
  isEncrypted,
  isVerified = false,
  size = 'md',
  showLabel = false,
  className = ''
}) => {
  const iconSize = {
    sm: 'w-3 h-3',
    md: 'w-4 h-4', 
    lg: 'w-5 h-5'
  }[size];

  const labelSize = {
    sm: 'text-xs',
    md: 'text-sm',
    lg: 'text-base'
  }[size];

  if (!isEncrypted) {
    return showLabel ? (
      <div className={`flex items-center gap-1 text-gray-500 ${className}`}>
        <Shield className={`${iconSize} text-gray-400`} aria-hidden="true" />
        <span className={labelSize}>Not encrypted</span>
      </div>
    ) : null;
  }

  const icon = isVerified ? (
    <ShieldCheck 
      className={`${iconSize} text-green-500`} 
      aria-label="Encrypted and verified"
    />
  ) : (
    <Shield 
      className={`${iconSize} text-blue-500`} 
      aria-label="Encrypted"
    />
  );

  if (showLabel) {
    return (
      <div className={`flex items-center gap-1 ${className}`}>
        {icon}
        <span className={`${labelSize} ${isVerified ? 'text-green-600' : 'text-blue-600'}`}>
          {isVerified ? 'Verified' : 'Encrypted'}
        </span>
      </div>
    );
  }

  return <div className={className}>{icon}</div>;
};

// Message Timestamp Component
export const MessageTimestamp: React.FC<MessageTimestampProps> = ({
  timestamp,
  editedAt,
  showDate = false,
  className = ''
}) => {
  const formatTime = (date: Date) => {
    return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
  };

  const formatDate = (date: Date) => {
    const today = new Date();
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    
    if (date.toDateString() === today.toDateString()) {
      return 'Today';
    } else if (date.toDateString() === yesterday.toDateString()) {
      return 'Yesterday';
    } else {
      return date.toLocaleDateString();
    }
  };

  return (
    <div className={`text-xs text-gray-500 ${className}`}>
      {showDate && (
        <span className="block">{formatDate(timestamp)}</span>
      )}
      <span>{formatTime(timestamp)}</span>
      {editedAt && (
        <span className="ml-1 italic" title={`Edited at ${formatTime(editedAt)}`}>
          (edited)
        </span>
      )}
    </div>
  );
};

// Message Status Component
export const MessageStatus: React.FC<MessageStatusProps> = ({
  status,
  timestamp,
  isOwn,
  className = ''
}) => {
  const getStatusIcon = () => {
    switch (status) {
      case 'sending':
        return <Loader2 className="w-3 h-3 animate-spin" aria-label="Sending" />;
      case 'sent':
        return <Check className="w-3 h-3" aria-label="Sent" />;
      case 'delivered':
        return <CheckCheck className="w-3 h-3" aria-label="Delivered" />;
      case 'read':
        return <Eye className="w-3 h-3 text-blue-500" aria-label="Read" />;
      case 'failed':
        return <AlertCircle className="w-3 h-3 text-red-500" aria-label="Failed" />;
      default:
        return <Clock className="w-3 h-3" aria-label="Pending" />;
    }
  };

  const getStatusColor = () => {
    switch (status) {
      case 'read':
        return 'text-blue-500';
      case 'failed':
        return 'text-red-500';
      case 'sending':
        return 'text-gray-400';
      default:
        return 'text-gray-500';
    }
  };

  if (!isOwn) return null;

  return (
    <div className={`flex items-center gap-1 ${getStatusColor()} ${className}`}>
      {getStatusIcon()}
      <MessageTimestamp timestamp={timestamp} className="text-inherit" />
    </div>
  );
};

// Typing Indicator Component
export const TypingIndicator: React.FC<TypingIndicatorProps> = ({
  users,
  className = ''
}) => {
  if (users.length === 0) return null;

  const getTypingText = () => {
    if (users.length === 1) {
      return `${users[0]} is typing...`;
    } else if (users.length === 2) {
      return `${users[0]} and ${users[1]} are typing...`;
    } else {
      return `${users[0]} and ${users.length - 1} others are typing...`;
    }
  };

  return (
    <div className={`flex items-center gap-3 px-4 py-2 text-sm text-gray-500 ${className}`}>
      <div className="flex gap-1">
        <div 
          className="w-2 h-2 bg-gray-400 rounded-full animate-bounce"
          style={{ animationDelay: '0ms', animationDuration: '1.4s' }}
          aria-hidden="true"
        />
        <div 
          className="w-2 h-2 bg-gray-400 rounded-full animate-bounce"
          style={{ animationDelay: '150ms', animationDuration: '1.4s' }}
          aria-hidden="true"
        />
        <div 
          className="w-2 h-2 bg-gray-400 rounded-full animate-bounce"
          style={{ animationDelay: '300ms', animationDuration: '1.4s' }}
          aria-hidden="true"
        />
      </div>
      <span aria-live="polite">{getTypingText()}</span>
    </div>
  );
};

// Message Bubble Component
export const MessageBubble: React.FC<MessageBubbleProps> = ({
  message,
  showSender = false,
  senderName,
  isGrouped = false,
  onRetry,
  className = ''
}) => {
  const {
    id,
    content,
    timestamp,
    isEncrypted,
    status,
    isOwn,
    type = 'text',
    editedAt,
  } = message;

  const handleRetry = () => {
    if (onRetry && status === 'failed') {
      onRetry(id);
    }
  };

  const bubbleClasses = useMemo(() => {
    const baseClasses = 'max-w-xs lg:max-w-md px-4 py-2 rounded-lg break-words';
    const ownClasses = 'bg-blue-500 text-white ml-auto';
    const otherClasses = 'bg-white border border-gray-200 text-gray-900';
    const failedClasses = 'border-red-200 bg-red-50';
    
    let classes = baseClasses;
    
    if (isOwn) {
      classes += ' ' + ownClasses;
    } else {
      classes += ' ' + otherClasses;
    }
    
    if (status === 'failed') {
      classes += ' ' + failedClasses;
    }
    
    // Rounded corner adjustments for grouped messages
    if (isGrouped && isOwn) {
      classes = classes.replace('rounded-lg', 'rounded-l-lg rounded-tr-lg rounded-br-sm');
    } else if (isGrouped && !isOwn) {
      classes = classes.replace('rounded-lg', 'rounded-r-lg rounded-tl-lg rounded-bl-sm');
    }
    
    return classes;
  }, [isOwn, status, isGrouped]);

  const systemMessage = type === 'system';

  if (systemMessage) {
    return (
      <div className={`flex justify-center my-4 ${className}`}>
        <div className="bg-gray-100 text-gray-600 text-sm px-3 py-1 rounded-full">
          {content}
        </div>
      </div>
    );
  }

  return (
    <div className={`flex ${isOwn ? 'justify-end' : 'justify-start'} group ${className}`}>
      <div className="space-y-1">
        {showSender && !isOwn && senderName && (
          <div className="text-xs text-gray-500 px-1">
            {senderName}
          </div>
        )}
        
        <div className={bubbleClasses}>
          <div className="space-y-1">
            {/* Message content */}
            <div className="text-sm">
              {content}
            </div>
            
            {/* Message metadata */}
            <div className={`flex items-center justify-between gap-2 text-xs ${
              isOwn ? 'text-blue-100' : 'text-gray-500'
            }`}>
              <div className="flex items-center gap-1">
                <MessageTimestamp 
                  timestamp={timestamp} 
                  editedAt={editedAt}
                  className="text-inherit" 
                />
                {isEncrypted && (
                  <EncryptionIndicator
                    isEncrypted={true}
                    size="sm"
                    className="ml-1"
                  />
                )}
              </div>
              
              {isOwn && (
                <MessageStatus
                  status={status}
                  timestamp={timestamp}
                  isOwn={true}
                  className="text-inherit"
                />
              )}
            </div>
            
            {/* Retry button for failed messages */}
            {status === 'failed' && onRetry && (
              <button
                onClick={handleRetry}
                className="text-xs text-red-600 hover:text-red-700 underline focus:outline-none focus:ring-2 focus:ring-red-500 focus:ring-offset-2 rounded"
                aria-label="Retry sending message"
              >
                Retry
              </button>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

// Message Date Separator Component
export const MessageDateSeparator: React.FC<{ date: Date }> = ({ date }) => {
  const formatDate = (date: Date) => {
    const today = new Date();
    const yesterday = new Date(today);
    yesterday.setDate(yesterday.getDate() - 1);
    
    if (date.toDateString() === today.toDateString()) {
      return 'Today';
    } else if (date.toDateString() === yesterday.toDateString()) {
      return 'Yesterday';
    } else {
      return date.toLocaleDateString(undefined, { 
        weekday: 'long', 
        year: 'numeric', 
        month: 'long', 
        day: 'numeric' 
      });
    }
  };

  return (
    <div className="flex items-center justify-center my-4">
      <div className="bg-gray-100 text-gray-600 text-xs px-3 py-1 rounded-full border">
        {formatDate(date)}
      </div>
    </div>
  );
};

// Message List Component
export interface MessageListProps {
  messages: Message[];
  currentUserId: string;
  getUserName?: (userId: string) => string;
  onRetryMessage?: (messageId: string) => void;
  typingUsers?: string[];
  className?: string;
}

export const MessageList: React.FC<MessageListProps> = ({
  messages,
  currentUserId,
  getUserName,
  onRetryMessage,
  typingUsers = [],
  className = ''
}) => {
  const shouldShowDateSeparator = (currentMsg: Message, prevMsg?: Message) => {
    if (!prevMsg) return true;
    
    const currentDate = new Date(currentMsg.timestamp).toDateString();
    const prevDate = new Date(prevMsg.timestamp).toDateString();
    
    return currentDate !== prevDate;
  };

  const isGroupedMessage = (currentMsg: Message, prevMsg?: Message) => {
    if (!prevMsg) return false;
    
    const timeDiff = currentMsg.timestamp.getTime() - prevMsg.timestamp.getTime();
    const fiveMinutes = 5 * 60 * 1000;
    
    return (
      prevMsg.senderId === currentMsg.senderId &&
      timeDiff <= fiveMinutes &&
      prevMsg.type !== 'system' &&
      currentMsg.type !== 'system'
    );
  };

  return (
    <div className={`space-y-2 ${className}`}>
      {messages.map((message, index) => {
        const prevMessage = index > 0 ? messages[index - 1] : undefined;
        const showDateSeparator = shouldShowDateSeparator(message, prevMessage);
        const isGrouped = isGroupedMessage(message, prevMessage);
        const showSender = !message.isOwn && (!isGrouped || !prevMessage);

        return (
          <React.Fragment key={message.id}>
            {showDateSeparator && (
              <MessageDateSeparator date={message.timestamp} />
            )}
            
            <MessageBubble
              message={message}
              showSender={showSender}
              senderName={getUserName?.(message.senderId)}
              isGrouped={isGrouped}
              onRetry={onRetryMessage}
            />
          </React.Fragment>
        );
      })}
      
      {typingUsers.length > 0 && (
        <TypingIndicator users={typingUsers} />
      )}
    </div>
  );
};

// Export all components
export {
  MessageBubble,
  MessageStatus,
  TypingIndicator,
  MessageTimestamp,
  EncryptionIndicator,
  MessageDateSeparator,
  MessageList
};