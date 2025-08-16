import React, { useEffect } from 'react'
import { Routes, Route, Navigate } from 'react-router-dom'
import { Box } from '@mui/material'
import { useAppSelector, useAppDispatch } from './hooks/redux'
import { loadFromStorage } from './store/slices/authSlice'
import LoginPage from './pages/LoginPage'
import RegisterPage from './pages/RegisterPage'
import ChatPage from './pages/ChatPage'
import SettingsPage from './pages/SettingsPage'
import { SecurityContextProvider } from './contexts/SecurityContext'
import { ChatContextProvider } from './contexts/ChatContext'
import LoadingScreen from './components/LoadingScreen'
import ErrorBoundary from './components/ErrorBoundary'

function App() {
  const dispatch = useAppDispatch()
  const { isAuthenticated, isLoading } = useAppSelector((state) => state.auth)

  useEffect(() => {
    // Load authentication state from localStorage on app startup
    console.log('App: Loading auth state from storage')
    
    // For debugging: Check what's in localStorage
    const token = localStorage.getItem('auth_token')
    const user = localStorage.getItem('user')
    console.log('App: LocalStorage contents:', { token: !!token, user: !!user })
    
    dispatch(loadFromStorage())
  }, [dispatch])

  console.log('App: Current auth state:', { isAuthenticated, isLoading })

  if (isLoading) {
    return <LoadingScreen />
  }

  return (
    <ErrorBoundary>
      <SecurityContextProvider>
        <ChatContextProvider>
          <Box sx={{ height: '100vh', overflow: 'hidden' }}>
            <Routes>
              {/* Public Routes */}
              <Route 
                path="/login" 
                element={!isAuthenticated ? <LoginPage /> : <Navigate to="/chat" replace />} 
              />
              <Route 
                path="/register" 
                element={!isAuthenticated ? <RegisterPage /> : <Navigate to="/chat" replace />} 
              />
              
              {/* Protected Routes */}
              <Route 
                path="/chat/*" 
                element={isAuthenticated ? <ChatPage /> : <Navigate to="/login" replace />} 
              />
              <Route 
                path="/settings" 
                element={isAuthenticated ? <SettingsPage /> : <Navigate to="/login" replace />} 
              />
              
              {/* Default Route */}
              <Route 
                path="/" 
                element={<Navigate to={isAuthenticated ? "/chat" : "/login"} replace />} 
              />
              
              {/* Catch All */}
              <Route 
                path="*" 
                element={<Navigate to="/" replace />} 
              />
            </Routes>
          </Box>
        </ChatContextProvider>
      </SecurityContextProvider>
    </ErrorBoundary>
  )
}

export default App