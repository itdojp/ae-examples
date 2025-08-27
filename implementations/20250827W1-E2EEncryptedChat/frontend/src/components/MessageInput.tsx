import React, { useState } from 'react';

interface MessageInputProps {
  onSend: (message: string) => void;
  isEncrypted: boolean;
}

export default function MessageInput({ onSend, isEncrypted }: MessageInputProps) {
  const [message, setMessage] = useState('');

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    if (message.trim()) {
      onSend(message);
      setMessage('');
    }
  };

  return (
    <form onSubmit={handleSubmit} className="bg-white border-t border-gray-200 p-4">
      <div className="flex items-center space-x-2">
        <input
          type="text"
          value={message}
          onChange={(e) => setMessage(e.target.value)}
          placeholder={isEncrypted ? "Type a message (encrypted)..." : "Waiting for encryption..."}
          className="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
          disabled={!isEncrypted}
        />
        <button
          type="submit"
          disabled={!isEncrypted || !message.trim()}
          className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition duration-200 disabled:opacity-50 disabled:cursor-not-allowed"
        >
          Send
        </button>
      </div>
      {isEncrypted && (
        <p className="text-xs text-green-600 mt-2">🔒 Messages are end-to-end encrypted</p>
      )}
    </form>
  );
}