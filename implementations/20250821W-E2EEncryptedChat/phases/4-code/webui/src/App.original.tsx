import React from 'react';
import { Provider } from 'react-redux';
import { ThemeProvider, CssBaseline } from '@mui/material';
import { store } from '@/store';
import { theme } from '@/styles/theme';
import ChatInterface from '@/components/ChatInterface';
import '@/styles/global.css';

function App() {
  console.log('=== App Component Initialization ===');
  console.log('Environment variables:', {
    VITE_API_URL: import.meta.env.VITE_API_URL,
    VITE_WS_URL: import.meta.env.VITE_WS_URL
  });
  console.log('Store state:', store.getState());
  
  return (
    <Provider store={store}>
      <ThemeProvider theme={theme}>
        <CssBaseline />
        <ChatInterface />
      </ThemeProvider>
    </Provider>
  );
}

export default App;