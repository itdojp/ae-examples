import React, { useState, useEffect, useRef } from 'react'
import {
  Box,
  Paper,
  TextField,
  IconButton,
  Typography,
  List,
  ListItem,
  ListItemText,
  Avatar,
  Divider,
  AppBar,
  Toolbar,
  Button,
  Badge,
} from '@mui/material'
import {
  Send,
  Security,
  Verified,
  Person,
  Logout,
} from '@mui/icons-material'
import { useAppDispatch, useAppSelector } from '../hooks/redux'
import { logout } from '../store/slices/authSlice'
import { loadContacts, loadConversations } from '../store/slices/chatSlice'

interface Message {
  id: string
  text: string
  sender: 'user' | 'contact'
  timestamp: number
  encrypted: boolean
}

const ChatInterface: React.FC = () => {
  const dispatch = useAppDispatch()
  const { user } = useAppSelector((state) => state.auth)
  const { contacts, conversations, isConnected } = useAppSelector((state) => state.chat)
  
  const [messages, setMessages] = useState<Message[]>([
    {
      id: '1',
      text: 'Welcome to SecureChat! This is a demonstration message showing E2E encryption.',
      sender: 'contact',
      timestamp: Date.now() - 120000,
      encrypted: true,
    },
    {
      id: '2', 
      text: 'All messages are encrypted with AES-256-GCM and protected by Perfect Forward Secrecy.',
      sender: 'contact',
      timestamp: Date.now() - 60000,
      encrypted: true,
    },
  ])
  
  const [newMessage, setNewMessage] = useState('')
  const [selectedContact, setSelectedContact] = useState<any>(null)
  const messagesEndRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    // Load initial data
    dispatch(loadContacts())
    dispatch(loadConversations())
  }, [dispatch])

  useEffect(() => {
    // Auto-scroll to bottom when new messages arrive
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' })
  }, [messages])

  const handleSendMessage = () => {
    if (newMessage.trim()) {
      const message: Message = {
        id: Date.now().toString(),
        text: newMessage,
        sender: 'user',
        timestamp: Date.now(),
        encrypted: true,
      }
      
      setMessages(prev => [...prev, message])
      setNewMessage('')
      
      // Simulate response (in real app, this would come via WebSocket)
      setTimeout(() => {
        const response: Message = {
          id: (Date.now() + 1).toString(),
          text: `Echo: ${newMessage} (This is a demo response)`,
          sender: 'contact',
          timestamp: Date.now(),
          encrypted: true,
        }
        setMessages(prev => [...prev, response])
      }, 1000)
    }
  }

  const handleKeyPress = (event: React.KeyboardEvent) => {
    if (event.key === 'Enter' && !event.shiftKey) {
      event.preventDefault()
      handleSendMessage()
    }
  }

  const handleLogout = async () => {
    await dispatch(logout())
  }

  return (
    <Box sx={{ height: '100vh', display: 'flex' }}>
      {/* Sidebar */}
      <Paper 
        sx={{ 
          width: 320, 
          display: 'flex', 
          flexDirection: 'column',
          borderRadius: 0,
          borderRight: '1px solid #e0e0e0',
        }}
      >
        {/* Header */}
        <AppBar position="static" sx={{ bgcolor: '#00b894' }}>
          <Toolbar>
            <Security sx={{ mr: 2 }} />
            <Typography variant="h6" sx={{ flexGrow: 1 }}>
              SecureChat
            </Typography>
            <Button 
              color="inherit" 
              onClick={handleLogout}
              startIcon={<Logout />}
              size="small"
            >
              Logout
            </Button>
          </Toolbar>
        </AppBar>

        {/* User Info */}
        <Box sx={{ p: 2, bgcolor: '#f5f5f5' }}>
          <Box sx={{ display: 'flex', alignItems: 'center', mb: 1 }}>
            <Avatar sx={{ mr: 2, bgcolor: '#00b894' }}>
              <Person />
            </Avatar>
            <Box>
              <Typography variant="subtitle1" fontWeight="bold">
                {user?.displayName || 'User'}
              </Typography>
              <Box sx={{ display: 'flex', alignItems: 'center' }}>
                <Badge 
                  color={isConnected ? 'success' : 'error'} 
                  variant="dot" 
                  sx={{ mr: 1 }}
                />
                <Typography variant="caption" color="text.secondary">
                  {isConnected ? 'Connected' : 'Offline'}
                </Typography>
                <Verified sx={{ ml: 1, fontSize: 16, color: '#00b894' }} />
              </Box>
            </Box>
          </Box>
        </Box>

        <Divider />

        {/* Contacts List */}
        <Box sx={{ flexGrow: 1, overflow: 'auto' }}>
          <Typography variant="subtitle2" sx={{ p: 2, color: 'text.secondary' }}>
            Contacts ({contacts.length})
          </Typography>
          <List dense>
            {contacts.map((contact) => (
              <ListItem
                key={contact.id}
                button
                selected={selectedContact?.id === contact.id}
                onClick={() => setSelectedContact(contact)}
                sx={{
                  '&.Mui-selected': {
                    backgroundColor: '#e8f5e8',
                  },
                }}
              >
                <Avatar sx={{ mr: 2, bgcolor: contact.isOnline ? '#00b894' : '#bdc3c7' }}>
                  {contact.displayName[0]}
                </Avatar>
                <ListItemText
                  primary={contact.displayName}
                  secondary={
                    <Box sx={{ display: 'flex', alignItems: 'center' }}>
                      <Typography variant="caption" color="text.secondary">
                        {contact.verificationStatus === 'verified' ? 'Verified' : 'Unverified'}
                      </Typography>
                      {contact.verificationStatus === 'verified' && (
                        <Verified sx={{ ml: 0.5, fontSize: 12, color: '#00b894' }} />
                      )}
                    </Box>
                  }
                />
              </ListItem>
            ))}
            
            {contacts.length === 0 && (
              <ListItem>
                <ListItemText
                  primary="No contacts yet"
                  secondary="Demo contacts will be loaded"
                  sx={{ textAlign: 'center', color: 'text.secondary' }}
                />
              </ListItem>
            )}
          </List>
        </Box>
      </Paper>

      {/* Chat Area */}
      <Box sx={{ flexGrow: 1, display: 'flex', flexDirection: 'column' }}>
        {/* Chat Header */}
        <Paper 
          sx={{ 
            p: 2, 
            borderRadius: 0, 
            borderBottom: '1px solid #e0e0e0',
            bgcolor: '#fafafa',
          }}
        >
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <Security sx={{ mr: 2, color: '#00b894' }} />
            <Box>
              <Typography variant="h6">
                {selectedContact ? selectedContact.displayName : 'SecureChat Demo'}
              </Typography>
              <Box sx={{ display: 'flex', alignItems: 'center' }}>
                <Typography variant="caption" color="text.secondary">
                  🔐 End-to-end encrypted
                </Typography>
                <Verified sx={{ ml: 1, fontSize: 16, color: '#00b894' }} />
              </Box>
            </Box>
          </Box>
        </Paper>

        {/* Messages */}
        <Box 
          sx={{ 
            flexGrow: 1, 
            overflow: 'auto', 
            p: 2,
            bgcolor: '#f8f9fa',
          }}
        >
          {messages.map((message) => (
            <Box
              key={message.id}
              sx={{
                display: 'flex',
                justifyContent: message.sender === 'user' ? 'flex-end' : 'flex-start',
                mb: 2,
              }}
            >
              <Paper
                sx={{
                  p: 2,
                  maxWidth: '70%',
                  bgcolor: message.sender === 'user' ? '#00b894' : 'white',
                  color: message.sender === 'user' ? 'white' : 'text.primary',
                  borderRadius: 2,
                  position: 'relative',
                }}
              >
                <Typography variant="body1">
                  {message.text}
                </Typography>
                <Box sx={{ display: 'flex', alignItems: 'center', mt: 1 }}>
                  <Typography 
                    variant="caption" 
                    sx={{ 
                      opacity: 0.7,
                      color: message.sender === 'user' ? 'white' : 'text.secondary',
                    }}
                  >
                    {new Date(message.timestamp).toLocaleTimeString()}
                  </Typography>
                  {message.encrypted && (
                    <Security 
                      sx={{ 
                        ml: 1, 
                        fontSize: 12, 
                        opacity: 0.7,
                        color: message.sender === 'user' ? 'white' : '#00b894',
                      }} 
                    />
                  )}
                </Box>
              </Paper>
            </Box>
          ))}
          <div ref={messagesEndRef} />
        </Box>

        {/* Message Input */}
        <Paper 
          sx={{ 
            p: 2, 
            borderRadius: 0, 
            borderTop: '1px solid #e0e0e0',
          }}
        >
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <TextField
              fullWidth
              multiline
              maxRows={3}
              placeholder="Type a secure message..."
              value={newMessage}
              onChange={(e) => setNewMessage(e.target.value)}
              onKeyPress={handleKeyPress}
              variant="outlined"
              size="small"
              sx={{ mr: 1 }}
            />
            <IconButton
              color="primary"
              onClick={handleSendMessage}
              disabled={!newMessage.trim()}
              sx={{
                bgcolor: '#00b894',
                color: 'white',
                '&:hover': { bgcolor: '#00a085' },
                '&:disabled': { bgcolor: '#bdc3c7' },
              }}
            >
              <Send />
            </IconButton>
          </Box>
          
          <Box sx={{ display: 'flex', alignItems: 'center', mt: 1 }}>
            <Security sx={{ fontSize: 14, color: '#00b894', mr: 0.5 }} />
            <Typography variant="caption" color="text.secondary">
              Messages are end-to-end encrypted. Only you and the recipient can read them.
            </Typography>
          </Box>
        </Paper>
      </Box>
    </Box>
  )
}

export default ChatInterface