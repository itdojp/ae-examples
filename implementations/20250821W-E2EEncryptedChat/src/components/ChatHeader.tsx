import React from 'react';
import { User } from '../domain/entities/User';

interface ChatHeaderProps {
  participant?: User;
  isVerified: boolean;
  onVerify: () => void;
}

const ChatHeader: React.FC<ChatHeaderProps> = ({ participant, isVerified, onVerify }) => {
  return (
    <div className="chat-header">
      <div className="participant-info">
        <div className="avatar">
          {participant?.displayName.charAt(0).toUpperCase()}
        </div>
        <div className="participant-details">
          <h2>{participant?.displayName || 'Unknown User'}</h2>
          <div className="verification-status">
            {isVerified ? (
              <span className="verified">✓ Verified</span>
            ) : (
              <button onClick={onVerify} className="verify-button">
                Verify Security Number
              </button>
            )}
          </div>
        </div>
      </div>
      
      <style jsx>{`
        .chat-header {
          display: flex;
          align-items: center;
          padding: 16px;
          background-color: #ffffff;
          border-bottom: 1px solid #e0e0e0;
          box-shadow: 0 2px 4px rgba(0, 0, 0, 0.05);
        }
        
        .participant-info {
          display: flex;
          align-items: center;
          gap: 12px;
        }
        
        .avatar {
          width: 40px;
          height: 40px;
          border-radius: 50%;
          background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
          display: flex;
          align-items: center;
          justify-content: center;
          color: white;
          font-weight: bold;
          font-size: 18px;
        }
        
        .participant-details h2 {
          margin: 0;
          font-size: 18px;
          font-weight: 600;
          color: #333;
        }
        
        .verification-status {
          margin-top: 4px;
        }
        
        .verified {
          color: #4caf50;
          font-size: 14px;
          font-weight: 500;
        }
        
        .verify-button {
          background: none;
          border: none;
          color: #1976d2;
          font-size: 14px;
          cursor: pointer;
          padding: 0;
          text-decoration: underline;
        }
        
        .verify-button:hover {
          color: #1565c0;
        }
      `}</style>
    </div>
  );
};

export default ChatHeader;