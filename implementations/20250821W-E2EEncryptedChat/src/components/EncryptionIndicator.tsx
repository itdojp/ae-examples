import React from 'react';

interface EncryptionIndicatorProps {
  status: 'active' | 'establishing' | 'error';
}

const EncryptionIndicator: React.FC<EncryptionIndicatorProps> = ({ status }) => {
  const statusConfig = {
    active: {
      icon: '🔒',
      text: 'End-to-End Encrypted',
      color: '#4caf50',
      bgColor: '#e8f5e9'
    },
    establishing: {
      icon: '🔄',
      text: 'Establishing encryption...',
      color: '#ff9800',
      bgColor: '#fff3e0'
    },
    error: {
      icon: '⚠️',
      text: 'Encryption error',
      color: '#f44336',
      bgColor: '#ffebee'
    }
  };

  const config = statusConfig[status];

  return (
    <div className="encryption-indicator" style={{ 
      backgroundColor: config.bgColor,
      color: config.color 
    }}>
      <span className="icon">{config.icon}</span>
      <span className="text">{config.text}</span>
      
      <style jsx>{`
        .encryption-indicator {
          display: flex;
          align-items: center;
          gap: 8px;
          padding: 8px 16px;
          font-size: 13px;
          font-weight: 500;
          transition: all 0.3s ease;
        }
        
        .icon {
          font-size: 16px;
          animation: ${status === 'establishing' ? 'spin 2s linear infinite' : 'none'};
        }
        
        @keyframes spin {
          from {
            transform: rotate(0deg);
          }
          to {
            transform: rotate(360deg);
          }
        }
        
        .text {
          font-size: 13px;
        }
      `}</style>
    </div>
  );
};

export default EncryptionIndicator;