import React from 'react';
import { EncryptedMessage } from '@e2e-chat/shared';

interface MessageListProps {
  messages: (EncryptedMessage & { content?: string })[];
  currentUserId: string;
}

export default function MessageList({ messages, currentUserId }: MessageListProps) {
  return (
    <>
      {messages.map((message) => {
        const isOwn = message.senderId === currentUserId;
        return (
          <div
            key={message.id}
            className={`flex ${isOwn ? 'justify-end' : 'justify-start'}`}
          >
            <div
              className={`max-w-xs lg:max-w-md px-4 py-2 rounded-lg ${
                isOwn
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-200 text-gray-800'
              }`}
            >
              <p className="break-words">{message.content || message.ciphertext || '[Message]'}</p>
              <p className={`text-xs mt-1 ${isOwn ? 'text-blue-100' : 'text-gray-500'}`}>
                {new Date(message.timestamp).toLocaleTimeString()}
              </p>
            </div>
          </div>
        );
      })}
    </>
  );
}