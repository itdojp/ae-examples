import React, { useState, useEffect, useRef } from 'react';
import { User } from '../domain/entities/User';
import { ChatAggregate } from '../domain/aggregates/ChatAggregate';
import { PlainMessage, MessageStatus } from '../domain/entities/Message';
import ChatHeader from './ChatHeader';
import MessageList from './MessageList';
import MessageInput from './MessageInput';
import EncryptionIndicator from './EncryptionIndicator';

interface ChatScreenProps {
  currentUser: User;
  chat: ChatAggregate;
  onSendMessage: (content: string) => Promise<void>;
  onVerifySession: () => void;
}

const ChatScreen: React.FC<ChatScreenProps> = ({
  currentUser,
  chat,
  onSendMessage,
  onVerifySession
}) => {
  const [messages, setMessages] = useState<PlainMessage[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [encryptionStatus, setEncryptionStatus] = useState<'active' | 'establishing' | 'error'>('establishing');
  const messagesEndRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const session = chat.getSession();
    if (session.ratchetState) {
      setEncryptionStatus('active');
    }
  }, [chat]);

  useEffect(() => {
    scrollToBottom();
  }, [messages]);

  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  const handleSendMessage = async (content: string) => {
    if (!content.trim() || isLoading) return;

    setIsLoading(true);
    try {
      const tempMessage: PlainMessage = {
        id: `temp_${Date.now()}`,
        senderId: currentUser.id,
        recipientId: chat.getOtherParticipant(currentUser)?.id || '',
        content,
        timestamp: new Date(),
        status: MessageStatus.SENDING
      };
      
      setMessages(prev => [...prev, tempMessage]);
      
      await onSendMessage(content);
      
      setMessages(prev => 
        prev.map(msg => 
          msg.id === tempMessage.id 
            ? { ...msg, status: MessageStatus.SENT }
            : msg
        )
      );
    } catch (error) {
      console.error('Failed to send message:', error);
      setEncryptionStatus('error');
    } finally {
      setIsLoading(false);
    }
  };

  const participant = chat.getOtherParticipant(currentUser);

  return (
    <div className="chat-screen">
      <ChatHeader 
        participant={participant}
        isVerified={chat.isVerified()}
        onVerify={onVerifySession}
      />
      
      <MessageList 
        messages={messages}
        currentUserId={currentUser.id}
      />
      <div ref={messagesEndRef} />
      
      <MessageInput 
        onSend={handleSendMessage}
        isEncrypted={true}
        disabled={isLoading || encryptionStatus === 'error'}
      />
      
      <EncryptionIndicator status={encryptionStatus} />

      <style jsx>{`
        .chat-screen {
          display: flex;
          flex-direction: column;
          height: 100vh;
          background-color: #f5f5f5;
        }
      `}</style>
    </div>
  );
};

export default ChatScreen;