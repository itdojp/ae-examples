import type { Meta, StoryObj } from '@storybook/react';
import React, { useState } from 'react';
import { ChatScreen } from '../../apps/web/app/chat/components/ChatScreen';
import { SecurityVerification } from '../../apps/web/app/chat/components/SecurityVerification';
import {
  MessageBubble,
  MessageStatus,
  TypingIndicator,
  MessageTimestamp,
  EncryptionIndicator,
  MessageList,
  MessageDateSeparator,
  type Message
} from '../../apps/web/app/chat/components/MessageComponents';

// Mock data
const mockCurrentUser = {
  id: 'user1',
  name: 'Alice',
  avatar: 'https://images.unsplash.com/photo-1494790108755-2616b5ad2a5a?w=32&h=32&fit=crop&crop=face',
  isOnline: true,
  publicKey: 'mock-public-key-1',
  isVerified: true
};

const mockOtherUser = {
  id: 'user2',
  name: 'Bob',
  avatar: 'https://images.unsplash.com/photo-1599566150163-29194dcaad36?w=32&h=32&fit=crop&crop=face',
  isOnline: true,
  lastSeen: new Date(Date.now() - 300000), // 5 minutes ago
  publicKey: 'mock-public-key-2',
  isVerified: false
};

const mockMessages: Message[] = [
  {
    id: '1',
    content: 'Hey! How are you doing?',
    senderId: 'user2',
    timestamp: new Date(Date.now() - 3600000), // 1 hour ago
    isEncrypted: true,
    status: 'read',
    isOwn: false,
    type: 'text'
  },
  {
    id: '2',
    content: "I'm doing great! Just finished working on the new security features.",
    senderId: 'user1',
    timestamp: new Date(Date.now() - 3500000),
    isEncrypted: true,
    status: 'read',
    isOwn: true,
    type: 'text'
  },
  {
    id: '3',
    content: 'That sounds awesome! Can you tell me more about it?',
    senderId: 'user2',
    timestamp: new Date(Date.now() - 3400000),
    isEncrypted: true,
    status: 'read',
    isOwn: false,
    type: 'text'
  },
  {
    id: '4',
    content: "Sure! We've implemented end-to-end encryption with perfect forward secrecy. Every message is encrypted using a unique key that's automatically deleted after use.",
    senderId: 'user1',
    timestamp: new Date(Date.now() - 3300000),
    isEncrypted: true,
    status: 'delivered',
    isOwn: true,
    type: 'text'
  },
  {
    id: '5',
    content: 'Wow, that sounds really secure!',
    senderId: 'user2',
    timestamp: new Date(Date.now() - 300000),
    isEncrypted: true,
    status: 'read',
    isOwn: false,
    type: 'text'
  },
  {
    id: '6',
    content: 'This message failed to send...',
    senderId: 'user1',
    timestamp: new Date(Date.now() - 60000),
    isEncrypted: true,
    status: 'failed',
    isOwn: true,
    type: 'text'
  },
  {
    id: '7',
    content: 'This message is currently being sent...',
    senderId: 'user1',
    timestamp: new Date(),
    isEncrypted: true,
    status: 'sending',
    isOwn: true,
    type: 'text'
  }
];

const mockVerificationData = {
  qrCode: 'data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iMTAwIiBoZWlnaHQ9IjEwMCIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4gPHJlY3Qgd2lkdGg9IjEwMCIgaGVpZ2h0PSIxMDAiIGZpbGw9ImJsYWNrIi8+IDx0ZXh0IHg9IjUwIiB5PSI1NSIgdGV4dC1hbmNob3I9Im1pZGRsZSIgZmlsbD0id2hpdGUiIGZvbnQtc2l6ZT0iMTAiPlFSPC90ZXh0PiA8L3N2Zz4=',
  securityNumber: {
    digits: '123456789012345678901234567890123456',
    formatted: '12345 67890 12345 67890 12345 67890 12345'
  },
  userPublicKey: 'mock-user-public-key',
  otherUserPublicKey: 'mock-other-user-public-key',
  verificationHash: 'mock-verification-hash'
};

// Meta configuration
const meta: Meta = {
  title: 'E2E Chat/Components',
  parameters: {
    layout: 'fullscreen',
    docs: {
      description: {
        component: 'End-to-End encrypted chat components with security verification and real-time messaging features.'
      }
    }
  },
  tags: ['autodocs']
};

export default meta;

// ChatScreen Stories
type ChatScreenStory = StoryObj<typeof ChatScreen>;

export const DefaultChatScreen: ChatScreenStory = {
  name: 'Chat Screen - Default',
  render: () => {
    const [messages, setMessages] = useState(mockMessages);
    const [showVerification, setShowVerification] = useState(false);

    const handleSendMessage = async (content: string) => {
      const newMessage: Message = {
        id: Date.now().toString(),
        content,
        senderId: 'user1',
        timestamp: new Date(),
        isEncrypted: true,
        status: 'sending',
        isOwn: true,
        type: 'text'
      };

      setMessages(prev => [...prev, newMessage]);

      // Simulate message processing
      setTimeout(() => {
        setMessages(prev => prev.map(msg => 
          msg.id === newMessage.id 
            ? { ...msg, status: Math.random() > 0.1 ? 'delivered' : 'failed' }
            : msg
        ));
      }, 1000);
    };

    return (
      <div className="h-screen">
        <ChatScreen
          chatId="chat1"
          currentUser={mockCurrentUser}
          otherUser={mockOtherUser}
          messages={messages}
          isOnline={true}
          isE2EEnabled={true}
          onSendMessage={handleSendMessage}
          onVerifyUser={() => setShowVerification(true)}
          typingUsers={['Bob']}
        />
        
        <SecurityVerification
          isOpen={showVerification}
          onClose={() => setShowVerification(false)}
          verificationData={mockVerificationData}
          otherUserName="Bob"
          onVerify={async () => {}}
        />
      </div>
    );
  }
};

export const ChatScreenOffline: ChatScreenStory = {
  name: 'Chat Screen - Offline',
  render: () => (
    <div className="h-screen">
      <ChatScreen
        chatId="chat1"
        currentUser={mockCurrentUser}
        otherUser={{ ...mockOtherUser, isOnline: false }}
        messages={mockMessages}
        isOnline={false}
        isE2EEnabled={true}
        onSendMessage={async () => {}}
        onVerifyUser={() => {}}
      />
    </div>
  )
};

export const ChatScreenUnverified: ChatScreenStory = {
  name: 'Chat Screen - Unverified',
  render: () => (
    <div className="h-screen">
      <ChatScreen
        chatId="chat1"
        currentUser={mockCurrentUser}
        otherUser={{ ...mockOtherUser, isVerified: false }}
        messages={mockMessages}
        isOnline={true}
        isE2EEnabled={true}
        onSendMessage={async () => {}}
        onVerifyUser={() => {}}
      />
    </div>
  )
};

export const ChatScreenNoEncryption: ChatScreenStory = {
  name: 'Chat Screen - No Encryption',
  render: () => (
    <div className="h-screen">
      <ChatScreen
        chatId="chat1"
        currentUser={mockCurrentUser}
        otherUser={mockOtherUser}
        messages={mockMessages.map(msg => ({ ...msg, isEncrypted: false }))}
        isOnline={true}
        isE2EEnabled={false}
        onSendMessage={async () => {}}
        onVerifyUser={() => {}}
      />
    </div>
  )
};

export const ChatScreenEmpty: ChatScreenStory = {
  name: 'Chat Screen - Empty',
  render: () => (
    <div className="h-screen">
      <ChatScreen
        chatId="chat1"
        currentUser={mockCurrentUser}
        otherUser={mockOtherUser}
        messages={[]}
        isOnline={true}
        isE2EEnabled={true}
        onSendMessage={async () => {}}
        onVerifyUser={() => {}}
      />
    </div>
  )
};

// SecurityVerification Stories
type SecurityVerificationStory = StoryObj<typeof SecurityVerification>;

export const SecurityVerificationDefault: SecurityVerificationStory = {
  name: 'Security Verification - Default',
  render: () => {
    const [isOpen, setIsOpen] = useState(true);
    
    return (
      <SecurityVerification
        isOpen={isOpen}
        onClose={() => setIsOpen(false)}
        verificationData={mockVerificationData}
        otherUserName="Bob"
        onVerify={async (verified) => {
          console.log('Verification result:', verified);
          setIsOpen(false);
        }}
      />
    );
  }
};

export const SecurityVerificationKeyChange: SecurityVerificationStory = {
  name: 'Security Verification - Key Changed',
  render: () => {
    const [isOpen, setIsOpen] = useState(true);
    
    return (
      <SecurityVerification
        isOpen={isOpen}
        onClose={() => setIsOpen(false)}
        verificationData={mockVerificationData}
        otherUserName="Bob"
        onVerify={async () => {}}
        hasKeyChanged={true}
        onKeyChange={(reason) => {
          console.log('Key change:', reason);
          setIsOpen(false);
        }}
      />
    );
  }
};

// Message Components Stories
export const MessageBubbleVariants = {
  name: 'Message Bubble - Variants',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50 min-h-screen">
      <h2 className="text-2xl font-bold mb-6">Message Bubble Variants</h2>
      
      <div className="space-y-4">
        <h3 className="text-lg font-semibold">Own Messages</h3>
        <MessageBubble
          message={{
            id: '1',
            content: 'This is my message with encryption',
            senderId: 'user1',
            timestamp: new Date(),
            isEncrypted: true,
            status: 'read',
            isOwn: true,
            type: 'text'
          }}
        />
        
        <MessageBubble
          message={{
            id: '2',
            content: 'This message failed to send',
            senderId: 'user1',
            timestamp: new Date(),
            isEncrypted: true,
            status: 'failed',
            isOwn: true,
            type: 'text'
          }}
          onRetry={() => console.log('Retry message')}
        />
        
        <MessageBubble
          message={{
            id: '3',
            content: 'This message is currently sending...',
            senderId: 'user1',
            timestamp: new Date(),
            isEncrypted: true,
            status: 'sending',
            isOwn: true,
            type: 'text'
          }}
        />
      </div>
      
      <div className="space-y-4">
        <h3 className="text-lg font-semibold">Other User Messages</h3>
        <MessageBubble
          message={{
            id: '4',
            content: 'This is a message from another user',
            senderId: 'user2',
            timestamp: new Date(),
            isEncrypted: true,
            status: 'read',
            isOwn: false,
            type: 'text'
          }}
          showSender={true}
          senderName="Bob"
        />
        
        <MessageBubble
          message={{
            id: '5',
            content: 'This message is not encrypted',
            senderId: 'user2',
            timestamp: new Date(),
            isEncrypted: false,
            status: 'read',
            isOwn: false,
            type: 'text'
          }}
          showSender={true}
          senderName="Bob"
        />
      </div>
      
      <div className="space-y-4">
        <h3 className="text-lg font-semibold">System Messages</h3>
        <MessageBubble
          message={{
            id: '6',
            content: 'Bob joined the conversation',
            senderId: 'system',
            timestamp: new Date(),
            isEncrypted: false,
            status: 'read',
            isOwn: false,
            type: 'system'
          }}
        />
      </div>
    </div>
  )
};

export const MessageStatusVariants = {
  name: 'Message Status - Variants',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50">
      <h2 className="text-2xl font-bold mb-6">Message Status Variants</h2>
      
      <div className="space-y-3">
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Sending</span>
          <MessageStatus status="sending" timestamp={new Date()} isOwn={true} />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Sent</span>
          <MessageStatus status="sent" timestamp={new Date()} isOwn={true} />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Delivered</span>
          <MessageStatus status="delivered" timestamp={new Date()} isOwn={true} />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Read</span>
          <MessageStatus status="read" timestamp={new Date()} isOwn={true} />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Failed</span>
          <MessageStatus status="failed" timestamp={new Date()} isOwn={true} />
        </div>
      </div>
    </div>
  )
};

export const TypingIndicatorVariants = {
  name: 'Typing Indicator - Variants',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50">
      <h2 className="text-2xl font-bold mb-6">Typing Indicator Variants</h2>
      
      <div className="space-y-3">
        <div className="bg-white rounded-lg">
          <TypingIndicator users={['Alice']} />
        </div>
        
        <div className="bg-white rounded-lg">
          <TypingIndicator users={['Alice', 'Bob']} />
        </div>
        
        <div className="bg-white rounded-lg">
          <TypingIndicator users={['Alice', 'Bob', 'Charlie']} />
        </div>
        
        <div className="bg-white rounded-lg">
          <TypingIndicator users={['Alice', 'Bob', 'Charlie', 'David', 'Eve']} />
        </div>
      </div>
    </div>
  )
};

export const EncryptionIndicatorVariants = {
  name: 'Encryption Indicator - Variants',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50">
      <h2 className="text-2xl font-bold mb-6">Encryption Indicator Variants</h2>
      
      <div className="space-y-4">
        <h3 className="text-lg font-semibold">Sizes</h3>
        <div className="flex items-center gap-4 p-4 bg-white rounded">
          <EncryptionIndicator isEncrypted={true} size="sm" showLabel />
          <EncryptionIndicator isEncrypted={true} size="md" showLabel />
          <EncryptionIndicator isEncrypted={true} size="lg" showLabel />
        </div>
        
        <h3 className="text-lg font-semibold">States</h3>
        <div className="space-y-3">
          <div className="flex items-center gap-4 p-3 bg-white rounded border">
            <span className="w-32">Not Encrypted:</span>
            <EncryptionIndicator isEncrypted={false} showLabel />
          </div>
          
          <div className="flex items-center gap-4 p-3 bg-white rounded border">
            <span className="w-32">Encrypted:</span>
            <EncryptionIndicator isEncrypted={true} showLabel />
          </div>
          
          <div className="flex items-center gap-4 p-3 bg-white rounded border">
            <span className="w-32">Verified:</span>
            <EncryptionIndicator isEncrypted={true} isVerified={true} showLabel />
          </div>
        </div>
        
        <h3 className="text-lg font-semibold">Icon Only</h3>
        <div className="flex items-center gap-4 p-4 bg-white rounded">
          <EncryptionIndicator isEncrypted={false} />
          <EncryptionIndicator isEncrypted={true} />
          <EncryptionIndicator isEncrypted={true} isVerified={true} />
        </div>
      </div>
    </div>
  )
};

export const MessageTimestampVariants = {
  name: 'Message Timestamp - Variants',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50">
      <h2 className="text-2xl font-bold mb-6">Message Timestamp Variants</h2>
      
      <div className="space-y-3">
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Time Only:</span>
          <MessageTimestamp timestamp={new Date()} />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>With Date:</span>
          <MessageTimestamp timestamp={new Date()} showDate />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Edited Message:</span>
          <MessageTimestamp 
            timestamp={new Date(Date.now() - 3600000)} 
            editedAt={new Date()} 
          />
        </div>
        
        <div className="flex items-center justify-between p-3 bg-white rounded border">
          <span>Yesterday:</span>
          <MessageTimestamp 
            timestamp={new Date(Date.now() - 86400000)} 
            showDate 
          />
        </div>
      </div>
    </div>
  )
};

export const MessageListComplete = {
  name: 'Message List - Complete',
  render: () => (
    <div className="h-screen bg-gray-50">
      <div className="h-full overflow-hidden">
        <MessageList
          messages={mockMessages}
          currentUserId="user1"
          getUserName={(userId) => userId === 'user1' ? 'Alice' : 'Bob'}
          onRetryMessage={(id) => console.log('Retry message:', id)}
          typingUsers={['Bob']}
          className="h-full overflow-y-auto px-4 py-6"
        />
      </div>
    </div>
  )
};

export const MessageDateSeparatorExample = {
  name: 'Message Date Separator - Example',
  render: () => (
    <div className="p-6 space-y-4 bg-gray-50">
      <h2 className="text-2xl font-bold mb-6">Date Separators</h2>
      
      <div className="space-y-4">
        <MessageDateSeparator date={new Date()} />
        <MessageDateSeparator date={new Date(Date.now() - 86400000)} />
        <MessageDateSeparator date={new Date(Date.now() - 86400000 * 7)} />
      </div>
    </div>
  )
};

// Interactive Playground
export const InteractivePlayground = {
  name: 'Interactive Playground',
  render: () => {
    const [messages, setMessages] = useState<Message[]>([]);
    const [showVerification, setShowVerification] = useState(false);
    const [isOnline, setIsOnline] = useState(true);
    const [isEncrypted, setIsEncrypted] = useState(true);
    const [isVerified, setIsVerified] = useState(false);

    const handleSendMessage = async (content: string) => {
      const newMessage: Message = {
        id: Date.now().toString(),
        content,
        senderId: 'user1',
        timestamp: new Date(),
        isEncrypted,
        status: 'sending',
        isOwn: true,
        type: 'text'
      };

      setMessages(prev => [...prev, newMessage]);

      // Simulate message processing
      setTimeout(() => {
        setMessages(prev => prev.map(msg => 
          msg.id === newMessage.id 
            ? { ...msg, status: Math.random() > 0.1 ? 'delivered' : 'failed' }
            : msg
        ));
      }, 1000);
    };

    const addIncomingMessage = () => {
      const messages = [
        'Hey there!',
        'How are you doing?',
        'This is a test message',
        'The security features look great!',
        'Can we schedule a call later?'
      ];

      const randomMessage = messages[Math.floor(Math.random() * messages.length)];
      
      const newMessage: Message = {
        id: Date.now().toString(),
        content: randomMessage,
        senderId: 'user2',
        timestamp: new Date(),
        isEncrypted,
        status: 'read',
        isOwn: false,
        type: 'text'
      };

      setMessages(prev => [...prev, newMessage]);
    };

    return (
      <div className="h-screen flex">
        <div className="flex-1">
          <ChatScreen
            chatId="playground"
            currentUser={mockCurrentUser}
            otherUser={{ ...mockOtherUser, isOnline, isVerified }}
            messages={messages}
            isOnline={isOnline}
            isE2EEnabled={isEncrypted}
            onSendMessage={handleSendMessage}
            onVerifyUser={() => setShowVerification(true)}
          />
        </div>
        
        <div className="w-80 bg-white border-l p-6 space-y-4">
          <h3 className="text-lg font-semibold">Playground Controls</h3>
          
          <div className="space-y-4">
            <div>
              <label className="flex items-center gap-2">
                <input
                  type="checkbox"
                  checked={isOnline}
                  onChange={(e) => setIsOnline(e.target.checked)}
                  className="rounded"
                />
                <span>Online</span>
              </label>
            </div>
            
            <div>
              <label className="flex items-center gap-2">
                <input
                  type="checkbox"
                  checked={isEncrypted}
                  onChange={(e) => setIsEncrypted(e.target.checked)}
                  className="rounded"
                />
                <span>Encryption Enabled</span>
              </label>
            </div>
            
            <div>
              <label className="flex items-center gap-2">
                <input
                  type="checkbox"
                  checked={isVerified}
                  onChange={(e) => setIsVerified(e.target.checked)}
                  className="rounded"
                />
                <span>Verified Contact</span>
              </label>
            </div>
            
            <button
              onClick={addIncomingMessage}
              className="w-full px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600"
            >
              Add Incoming Message
            </button>
            
            <button
              onClick={() => setShowVerification(true)}
              className="w-full px-4 py-2 bg-green-500 text-white rounded hover:bg-green-600"
            >
              Show Verification
            </button>
            
            <button
              onClick={() => setMessages([])}
              className="w-full px-4 py-2 bg-red-500 text-white rounded hover:bg-red-600"
            >
              Clear Messages
            </button>
          </div>
        </div>
        
        <SecurityVerification
          isOpen={showVerification}
          onClose={() => setShowVerification(false)}
          verificationData={mockVerificationData}
          otherUserName="Bob"
          onVerify={async (verified) => {
            setIsVerified(verified);
            setShowVerification(false);
          }}
        />
      </div>
    );
  }
};