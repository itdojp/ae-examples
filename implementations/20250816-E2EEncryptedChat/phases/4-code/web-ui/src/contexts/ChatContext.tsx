import React, { createContext, useContext, useEffect, ReactNode } from 'react'
import { useAppSelector } from '../hooks/redux'
import { websocketService } from '../services/websocketService'

interface ChatContextType {
  isConnected: boolean
  connect: () => void
  disconnect: () => void
}

const ChatContext = createContext<ChatContextType | undefined>(undefined)

interface ChatContextProviderProps {
  children: ReactNode
}

export const ChatContextProvider: React.FC<ChatContextProviderProps> = ({ children }) => {
  const { token, isAuthenticated } = useAppSelector((state) => state.auth)
  const { isConnected } = useAppSelector((state) => state.chat)

  useEffect(() => {
    if (isAuthenticated && token) {
      websocketService.connect(token)
    } else {
      websocketService.disconnect()
    }

    return () => {
      websocketService.disconnect()
    }
  }, [isAuthenticated, token])

  const connect = () => {
    if (token) {
      websocketService.connect(token)
    }
  }

  const disconnect = () => {
    websocketService.disconnect()
  }

  const value: ChatContextType = {
    isConnected,
    connect,
    disconnect,
  }

  return (
    <ChatContext.Provider value={value}>
      {children}
    </ChatContext.Provider>
  )
}

export const useChatContext = () => {
  const context = useContext(ChatContext)
  if (context === undefined) {
    throw new Error('useChatContext must be used within a ChatContextProvider')
  }
  return context
}