
// Simple Auth Test Component
import React, { useState } from 'react';
import { Box, Button, TextField, Alert, Typography } from '@mui/material';

const SimpleAuthTest = () => {
  const [email, setEmail] = useState('test@example.com');
  const [password, setPassword] = useState('password123');
  const [result, setResult] = useState('');
  const [loading, setLoading] = useState(false);

  const testDirectAPI = async () => {
    console.log('=== Direct API Test ===');
    setLoading(true);
    setResult('Testing...');

    try {
      // Direct fetch without any framework interference
      const response = await fetch('http://localhost:3000/api/auth/login', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ email, password })
      });

      console.log('Response status:', response.status);
      console.log('Response headers:', [...response.headers.entries()]);

      if (response.ok) {
        const data = await response.json();
        console.log('Login success:', data);
        setResult('SUCCESS: ' + JSON.stringify(data, null, 2));
        
        // Store token
        localStorage.setItem('authToken', data.token);
        
        // Trigger a page reload to test authentication state
        setTimeout(() => {
          window.location.reload();
        }, 2000);
        
      } else {
        const errorText = await response.text();
        console.error('Login failed:', response.status, errorText);
        setResult('FAILED: ' + response.status + ' - ' + errorText);
      }
    } catch (error) {
      console.error('Request error:', error);
      setResult('ERROR: ' + error.message);
    } finally {
      setLoading(false);
    }
  };

  const testRegistration = async () => {
    console.log('=== Registration Test ===');
    setLoading(true);
    setResult('Testing registration...');

    try {
      const timestamp = Date.now();
      const response = await fetch('http://localhost:3000/api/auth/register', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          username: `testuser${timestamp}`,
          email: `test${timestamp}@example.com`,
          password: 'password123'
        })
      });

      if (response.ok) {
        const data = await response.json();
        console.log('Registration success:', data);
        setResult('REGISTRATION SUCCESS: ' + JSON.stringify(data, null, 2));
      } else {
        const errorText = await response.text();
        console.error('Registration failed:', errorText);
        setResult('REGISTRATION FAILED: ' + errorText);
      }
    } catch (error) {
      console.error('Registration error:', error);
      setResult('REGISTRATION ERROR: ' + error.message);
    } finally {
      setLoading(false);
    }
  };

  const checkAuthState = () => {
    const token = localStorage.getItem('authToken');
    const envVars = {
      VITE_API_URL: import.meta.env.VITE_API_URL,
      VITE_WS_URL: import.meta.env.VITE_WS_URL
    };
    
    setResult('AUTH STATE: ' + JSON.stringify({
      hasToken: !!token,
      tokenPreview: token ? token.substring(0, 20) + '...' : null,
      envVars
    }, null, 2));
  };

  return (
    <Box sx={{ p: 4, maxWidth: 600, mx: 'auto' }}>
      <Typography variant="h4" gutterBottom>
        🔧 Auth Debug Tool
      </Typography>
      
      <Box sx={{ mb: 2 }}>
        <TextField
          fullWidth
          label="Email"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
          margin="normal"
        />
        <TextField
          fullWidth
          label="Password"
          type="password"
          value={password}
          onChange={(e) => setPassword(e.target.value)}
          margin="normal"
        />
      </Box>

      <Box sx={{ mb: 2 }}>
        <Button 
          variant="contained" 
          onClick={testDirectAPI} 
          disabled={loading}
          sx={{ mr: 1 }}
        >
          Test Login
        </Button>
        <Button 
          variant="outlined" 
          onClick={testRegistration} 
          disabled={loading}
          sx={{ mr: 1 }}
        >
          Test Registration
        </Button>
        <Button 
          variant="text" 
          onClick={checkAuthState}
        >
          Check State
        </Button>
      </Box>

      {result && (
        <Alert severity={result.includes('SUCCESS') ? 'success' : result.includes('ERROR') || result.includes('FAILED') ? 'error' : 'info'}>
          <pre style={{ whiteSpace: 'pre-wrap', fontSize: '12px' }}>
            {result}
          </pre>
        </Alert>
      )}
    </Box>
  );
};

export default SimpleAuthTest;
