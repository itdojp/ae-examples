import React from 'react';

interface EncryptionIndicatorProps {
  status: 'active' | 'establishing' | 'error';
}

export default function EncryptionIndicator({ status }: EncryptionIndicatorProps) {
  const statusConfig = {
    active: {
      icon: '🔒',
      text: 'End-to-end encrypted',
      color: 'text-green-600',
      bgColor: 'bg-green-50'
    },
    establishing: {
      icon: '🔄',
      text: 'Establishing encryption...',
      color: 'text-yellow-600',
      bgColor: 'bg-yellow-50'
    },
    error: {
      icon: '⚠️',
      text: 'Encryption error',
      color: 'text-red-600',
      bgColor: 'bg-red-50'
    }
  };

  const config = statusConfig[status];

  return (
    <div className={`flex items-center gap-2 px-3 py-1 rounded-full ${config.bgColor} ${config.color}`}>
      <span className="text-sm">{config.icon}</span>
      <span className="text-sm font-medium">{config.text}</span>
    </div>
  );
}