import React, { useState, useEffect, useRef } from 'react';
import { useNavigate } from 'react-router-dom';
import io, { Socket } from 'socket.io-client';
import toast from 'react-hot-toast';
import { User, EncryptedMessage, MessageEvent } from '@e2e-chat/shared';
import { useAuthStore } from '../stores/authStore';
import { authApi, messagesApi, keysApi } from '../services/api';
import { CryptoService } from '../services/crypto';
import MessageList from './MessageList';
import MessageInput from './MessageInput';
import UserList from './UserList';
import EncryptionIndicator from './EncryptionIndicator';

export default function Chat() {
  const navigate = useNavigate();
  const { user, token, keyPair, logout } = useAuthStore();
  const [socket, setSocket] = useState<Socket | null>(null);
  const [users, setUsers] = useState<User[]>([]);
  const [selectedUser, setSelectedUser] = useState<User | null>(null);
  const [messages, setMessages] = useState<EncryptedMessage[]>([]);
  const [encryptionStatus, setEncryptionStatus] = useState<'active' | 'establishing' | 'error'>('establishing');
  const [recipientPublicKey, setRecipientPublicKey] = useState<string | null>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  // Initialize socket connection
  useEffect(() => {
    if (!token) return;

    const newSocket = io('http://localhost:3001', {
      auth: { token }
    });

    newSocket.on('connect', () => {
      console.log('Connected to server');
      setEncryptionStatus('active');
    });

    newSocket.on('new-message', (event: MessageEvent) => {
      if (event.type === 'message') {
        handleIncomingMessage(event.data);
      }
    });

    newSocket.on('presence', (event: MessageEvent) => {
      if (event.type === 'presence') {
        // Update user online status
        console.log('User presence update:', event.data);
      }
    });

    setSocket(newSocket);

    return () => {
      newSocket.disconnect();
    };
  }, [token]);

  // Load users from API
  useEffect(() => {
    const fetchUsers = async () => {
      try {
        const response = await authApi.getUsers();
        setUsers(response.users);
      } catch (error) {
        console.error('Failed to fetch users:', error);
      }
    };

    if (token) {
      fetchUsers();
    }
  }, [token]);

  // Load messages when user is selected
  useEffect(() => {
    if (!selectedUser) return;

    loadConversation(selectedUser.id);
    loadRecipientKeys(selectedUser.id);
  }, [selectedUser]);

  // Scroll to bottom when messages update
  useEffect(() => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  }, [messages]);

  const loadConversation = async (userId: string) => {
    try {
      const { messages: encryptedMessages } = await messagesApi.getConversation(userId);
      
      // For now, just show the messages without decryption
      // Decryption will be added once we have proper key exchange
      setMessages(encryptedMessages || []);
    } catch (error) {
      console.error('Failed to load conversation:', error);
    }
  };

  const loadRecipientKeys = async (userId: string) => {
    try {
      const keys = await keysApi.getKeys(userId);
      setRecipientPublicKey(keys.identityKey);
      setEncryptionStatus('active');
    } catch (error) {
      console.error('Failed to load recipient keys:', error);
      setEncryptionStatus('error');
    }
  };

  const handleIncomingMessage = (message: EncryptedMessage) => {
    // Add message directly (decryption will be implemented properly later)
    setMessages(prev => [...prev, message]);
  };

  const sendMessage = async (content: string) => {
    if (!selectedUser) {
      toast.error('Please select a user');
      return;
    }

    try {
      let ciphertext = content;
      let nonce = 'temp-nonce';
      
      // Try to encrypt if keys are available
      if (recipientPublicKey && keyPair?.privateKey) {
        try {
          const encrypted = CryptoService.encrypt(
            content,
            recipientPublicKey,
            keyPair.privateKey
          );
          ciphertext = encrypted.ciphertext;
          nonce = encrypted.nonce;
        } catch (err) {
          console.warn('Encryption failed, sending as plain text:', err);
        }
      }

      // Send to server
      const response = await messagesApi.send(
        selectedUser.id,
        ciphertext,
        nonce,
        'auth-tag-placeholder'
      );

      // Emit via socket
      socket?.emit('send-message', {
        recipientId: selectedUser.id,
        message: response.message
      });

      // Add to local messages with original content
      setMessages(prev => [...prev, {
        ...response.message,
        content
      }]);
    } catch (error) {
      toast.error('Failed to send message');
      console.error('Send message error:', error);
    }
  };

  const handleLogout = () => {
    socket?.disconnect();
    logout();
    navigate('/login');
  };

  return (
    <div className="flex h-screen bg-gray-100">
      {/* Sidebar */}
      <div className="w-80 bg-white border-r border-gray-200 flex flex-col">
        <div className="p-4 border-b border-gray-200">
          <div className="flex items-center justify-between">
            <div>
              <h2 className="text-xl font-semibold">{user?.displayName}</h2>
              <p className="text-sm text-gray-500">{user?.email}</p>
            </div>
            <button
              onClick={handleLogout}
              className="text-gray-500 hover:text-gray-700"
            >
              Logout
            </button>
          </div>
        </div>
        <UserList
          users={users}
          selectedUser={selectedUser}
          onSelectUser={setSelectedUser}
        />
      </div>

      {/* Chat Area */}
      {selectedUser ? (
        <div className="flex-1 flex flex-col">
          {/* Chat Header */}
          <div className="bg-white border-b border-gray-200 p-4">
            <div className="flex items-center justify-between">
              <div>
                <h3 className="text-lg font-semibold">{selectedUser.displayName}</h3>
                <p className="text-sm text-gray-500">{selectedUser.email}</p>
              </div>
              <EncryptionIndicator status={encryptionStatus} />
            </div>
          </div>

          {/* Messages */}
          <div className="flex-1 overflow-y-auto p-4 space-y-4">
            <MessageList
              messages={messages}
              currentUserId={user?.id || ''}
            />
            <div ref={messagesEndRef} />
          </div>

          {/* Message Input */}
          <MessageInput
            onSend={sendMessage}
            isEncrypted={encryptionStatus === 'active'}
          />
        </div>
      ) : (
        <div className="flex-1 flex items-center justify-center">
          <div className="text-center">
            <p className="text-gray-500 text-lg">Select a user to start chatting</p>
            <p className="text-gray-400 mt-2">🔒 All messages are end-to-end encrypted</p>
          </div>
        </div>
      )}
    </div>
  );
}