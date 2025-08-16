import React, { createContext, useContext, useEffect, ReactNode } from 'react'
import { useAppDispatch, useAppSelector } from '../hooks/redux'
import { initializeEncryption } from '../store/slices/encryptionSlice'

interface SecurityContextType {
  isSecureEnvironment: boolean
  encryptionReady: boolean
  initializeSecurity: () => Promise<void>
}

const SecurityContext = createContext<SecurityContextType | undefined>(undefined)

interface SecurityContextProviderProps {
  children: ReactNode
}

export const SecurityContextProvider: React.FC<SecurityContextProviderProps> = ({ children }) => {
  const dispatch = useAppDispatch()
  const { user } = useAppSelector((state) => state.auth)
  const { isInitialized } = useAppSelector((state) => state.encryption)

  const isSecureEnvironment = typeof window !== 'undefined' && 
    window.crypto && 
    window.crypto.subtle && 
    window.isSecureContext

  const initializeSecurity = async () => {
    if (user && !isInitialized) {
      await dispatch(initializeEncryption(user.id))
    }
  }

  useEffect(() => {
    if (user && isSecureEnvironment) {
      initializeSecurity()
    }
  }, [user, isSecureEnvironment])

  const value: SecurityContextType = {
    isSecureEnvironment,
    encryptionReady: isInitialized,
    initializeSecurity,
  }

  return (
    <SecurityContext.Provider value={value}>
      {children}
    </SecurityContext.Provider>
  )
}

export const useSecurityContext = () => {
  const context = useContext(SecurityContext)
  if (context === undefined) {
    throw new Error('useSecurityContext must be used within a SecurityContextProvider')
  }
  return context
}