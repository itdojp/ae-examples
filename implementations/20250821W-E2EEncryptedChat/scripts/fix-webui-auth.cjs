// WebUI Authentication Fix
// Based on comprehensive testing, we know the backend works perfectly
// The issue is likely in the React component mounting or state management

const fs = require('fs');
const path = require('path');

console.log('=== WebUI Authentication Fix ===');

// 1. Create a simplified authentication test component
const simpleAuthTest = `
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
          username: \`testuser\${timestamp}\`,
          email: \`test\${timestamp}@example.com\`,
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
`;

// 2. Create a minimal App component that bypasses complex authentication logic
const minimalApp = `
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
`;

// Write the files
const webuiPath = '/home/claudecode/work/ae-framework_test/webui/src';

console.log('1. Creating SimpleAuthTest component...');
fs.writeFileSync(path.join(webuiPath, 'components/SimpleAuthTest.tsx'), simpleAuthTest);
console.log('   ✅ SimpleAuthTest.tsx created');

console.log('2. Backing up original App.tsx...');
const originalApp = fs.readFileSync(path.join(webuiPath, 'App.tsx'), 'utf8');
fs.writeFileSync(path.join(webuiPath, 'App.original.tsx'), originalApp);
console.log('   ✅ App.original.tsx created');

console.log('3. Creating minimal App.tsx...');
fs.writeFileSync(path.join(webuiPath, 'App.tsx'), minimalApp);
console.log('   ✅ Minimal App.tsx created');

console.log('4. Creating restore script...');
const restoreScript = `#!/bin/bash
# Restore original App.tsx
cp /home/claudecode/work/ae-framework_test/webui/src/App.original.tsx /home/claudecode/work/ae-framework_test/webui/src/App.tsx
echo "Original App.tsx restored"
`;

fs.writeFileSync('/home/claudecode/work/ae-framework_test/restore-app.sh', restoreScript);
fs.chmodSync('/home/claudecode/work/ae-framework_test/restore-app.sh', 0o755);
console.log('   ✅ Restore script created');

console.log('\n=== Fix Applied ===');
console.log('✅ Simplified authentication component created');
console.log('✅ Minimal App component created (bypasses Redux/complex state)');
console.log('✅ Original App backed up as App.original.tsx');
console.log('✅ Restore script created: ./restore-app.sh');

console.log('\n📋 Next Steps:');
console.log('1. Run: npm run build');
console.log('2. Test at: http://localhost:4173');
console.log('3. Use the debug buttons to test authentication directly');
console.log('4. If it works, we know the issue is in Redux/state management');
console.log('5. If it fails, we know the issue is in the browser environment');

console.log('\n🔄 To restore original: ./restore-app.sh');