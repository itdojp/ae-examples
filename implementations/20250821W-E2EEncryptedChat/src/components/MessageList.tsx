import React from 'react';
import { PlainMessage, MessageStatus } from '../domain/entities/Message';
import { UserId } from '../domain/entities/User';

interface MessageListProps {
  messages: PlainMessage[];
  currentUserId: UserId;
}

const MessageList: React.FC<MessageListProps> = ({ messages, currentUserId }) => {
  const getStatusIcon = (status: MessageStatus) => {
    switch (status) {
      case MessageStatus.SENDING:
        return '⏳';
      case MessageStatus.SENT:
        return '✓';
      case MessageStatus.DELIVERED:
        return '✓✓';
      case MessageStatus.READ:
        return '👁';
      case MessageStatus.FAILED:
        return '❌';
      default:
        return '';
    }
  };

  const formatTime = (date: Date) => {
    return new Date(date).toLocaleTimeString('en-US', {
      hour: '2-digit',
      minute: '2-digit'
    });
  };

  return (
    <div className="message-list">
      {messages.map((message) => {
        const isOwn = message.senderId === currentUserId;
        
        return (
          <div
            key={message.id}
            className={`message-wrapper ${isOwn ? 'own' : 'other'}`}
          >
            <div className={`message ${isOwn ? 'own-message' : 'other-message'}`}>
              <div className="message-content">{message.content}</div>
              <div className="message-meta">
                <span className="message-time">{formatTime(message.timestamp)}</span>
                {isOwn && (
                  <span className="message-status">{getStatusIcon(message.status)}</span>
                )}
              </div>
            </div>
          </div>
        );
      })}
      
      <style jsx>{`
        .message-list {
          flex: 1;
          overflow-y: auto;
          padding: 16px;
          background-color: #f5f5f5;
        }
        
        .message-wrapper {
          display: flex;
          margin-bottom: 12px;
        }
        
        .message-wrapper.own {
          justify-content: flex-end;
        }
        
        .message-wrapper.other {
          justify-content: flex-start;
        }
        
        .message {
          max-width: 70%;
          padding: 10px 14px;
          border-radius: 18px;
          word-wrap: break-word;
        }
        
        .own-message {
          background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
          color: white;
          border-bottom-right-radius: 4px;
        }
        
        .other-message {
          background-color: white;
          color: #333;
          border-bottom-left-radius: 4px;
          box-shadow: 0 1px 2px rgba(0, 0, 0, 0.1);
        }
        
        .message-content {
          font-size: 15px;
          line-height: 1.4;
          margin-bottom: 4px;
        }
        
        .message-meta {
          display: flex;
          gap: 6px;
          align-items: center;
          font-size: 12px;
          opacity: 0.7;
        }
        
        .own-message .message-meta {
          justify-content: flex-end;
        }
        
        .message-time {
          font-size: 11px;
        }
        
        .message-status {
          font-size: 14px;
        }
      `}</style>
    </div>
  );
};

export default MessageList;