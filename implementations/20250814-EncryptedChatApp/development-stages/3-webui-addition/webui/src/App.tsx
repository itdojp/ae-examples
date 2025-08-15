
import React from 'react';
import { ThemeProvider, CssBaseline, Container } from '@mui/material';
import { theme } from '@/styles/theme';
import SimpleAuthTest from './components/SimpleAuthTest';
import '@/styles/global.css';

function App() {
  console.log('=== Minimal App Starting ===');
  console.log('Environment:', {
    API_URL: import.meta.env.VITE_API_URL,
    WS_URL: import.meta.env.VITE_WS_URL
  });

  return (
    <ThemeProvider theme={theme}>
      <CssBaseline />
      <Container>
        <SimpleAuthTest />
      </Container>
    </ThemeProvider>
  );
}

export default App;
