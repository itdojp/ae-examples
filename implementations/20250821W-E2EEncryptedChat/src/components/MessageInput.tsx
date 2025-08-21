import React, { useState, KeyboardEvent } from 'react';

interface MessageInputProps {
  onSend: (message: string) => void;
  isEncrypted: boolean;
  disabled?: boolean;
}

const MessageInput: React.FC<MessageInputProps> = ({ onSend, isEncrypted, disabled }) => {
  const [message, setMessage] = useState('');

  const handleSend = () => {
    if (message.trim() && !disabled) {
      onSend(message);
      setMessage('');
    }
  };

  const handleKeyPress = (e: KeyboardEvent<HTMLTextAreaElement>) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSend();
    }
  };

  return (
    <div className="message-input-container">
      <div className="input-wrapper">
        {isEncrypted && (
          <div className="encryption-badge" title="Messages are end-to-end encrypted">
            🔒
          </div>
        )}
        <textarea
          className="message-input"
          placeholder="Type a message..."
          value={message}
          onChange={(e) => setMessage(e.target.value)}
          onKeyPress={handleKeyPress}
          disabled={disabled}
          rows={1}
        />
        <button 
          className="send-button" 
          onClick={handleSend}
          disabled={!message.trim() || disabled}
        >
          <svg width="24" height="24" viewBox="0 0 24 24" fill="none">
            <path 
              d="M2 21L23 12L2 3V10L17 12L2 14V21Z" 
              fill="currentColor"
            />
          </svg>
        </button>
      </div>
      
      <style jsx>{`
        .message-input-container {
          padding: 16px;
          background-color: white;
          border-top: 1px solid #e0e0e0;
        }
        
        .input-wrapper {
          display: flex;
          align-items: flex-end;
          gap: 12px;
          position: relative;
        }
        
        .encryption-badge {
          position: absolute;
          left: 12px;
          bottom: 12px;
          font-size: 16px;
          z-index: 1;
        }
        
        .message-input {
          flex: 1;
          padding: 12px 12px 12px 40px;
          border: 1px solid #e0e0e0;
          border-radius: 24px;
          font-size: 15px;
          resize: none;
          outline: none;
          font-family: inherit;
          line-height: 1.4;
          max-height: 120px;
          overflow-y: auto;
        }
        
        .message-input:focus {
          border-color: #667eea;
        }
        
        .message-input:disabled {
          background-color: #f5f5f5;
          cursor: not-allowed;
        }
        
        .send-button {
          width: 48px;
          height: 48px;
          border-radius: 50%;
          background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
          border: none;
          color: white;
          display: flex;
          align-items: center;
          justify-content: center;
          cursor: pointer;
          transition: transform 0.2s, opacity 0.2s;
        }
        
        .send-button:hover:not(:disabled) {
          transform: scale(1.05);
        }
        
        .send-button:active:not(:disabled) {
          transform: scale(0.95);
        }
        
        .send-button:disabled {
          opacity: 0.5;
          cursor: not-allowed;
        }
      `}</style>
    </div>
  );
};

export default MessageInput;