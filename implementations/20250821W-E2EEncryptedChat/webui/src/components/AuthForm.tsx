import React, { useState } from 'react';
import {
  Box,
  Paper,
  Typography,
  TextField,
  Button,
  Alert,
  Tabs,
  Tab,
  CircularProgress,
  Link,
} from '@mui/material';
import { useAuth } from '@/hooks';
import { apiService } from '@/services/apiService';

interface TabPanelProps {
  children?: React.ReactNode;
  index: number;
  value: number;
}

function TabPanel(props: TabPanelProps) {
  const { children, value, index, ...other } = props;
  return (
    <div
      role="tabpanel"
      hidden={value !== index}
      id={`auth-tabpanel-${index}`}
      aria-labelledby={`auth-tab-${index}`}
      {...other}
    >
      {value === index && <Box sx={{ p: 3 }}>{children}</Box>}
    </div>
  );
}

const AuthForm: React.FC = () => {
  const [tabValue, setTabValue] = useState(0);
  const [formData, setFormData] = useState({
    email: '',
    password: '',
    username: '',
    confirmPassword: '',
  });
  const [error, setError] = useState<string | null>(null);
  const [success, setSuccess] = useState<string | null>(null);
  const { login, loading } = useAuth();

  const handleTabChange = (event: React.SyntheticEvent, newValue: number) => {
    setTabValue(newValue);
    setError(null);
    setSuccess(null);
  };

  const handleInputChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    setFormData({
      ...formData,
      [e.target.name]: e.target.value,
    });
    setError(null);
  };

  const handleLogin = async (e: React.FormEvent) => {
    e.preventDefault();
    
    console.log('=== AuthForm Login Attempt ===');
    console.log('Form data:', { email: formData.email, password: '***' });
    
    if (!formData.email || !formData.password) {
      setError('Email and password are required');
      return;
    }

    try {
      console.log('Calling login hook...');
      const result = await login(formData.email, formData.password);
      console.log('Login hook result:', result);
      
      if (!result.success) {
        console.error('Login failed with result:', result);
        setError(result.error || 'Login failed');
      } else {
        console.log('Login successful!');
      }
    } catch (error) {
      console.error('Login exception:', error);
      setError('Login failed. Please try again.');
    }
  };

  const handleRegister = async (e: React.FormEvent) => {
    e.preventDefault();
    
    console.log('=== AuthForm Registration Attempt ===');
    console.log('Form data:', { 
      username: formData.username, 
      email: formData.email, 
      password: '***',
      confirmPassword: '***'
    });
    
    if (!formData.email || !formData.password || !formData.username) {
      setError('All fields are required');
      return;
    }

    if (formData.password !== formData.confirmPassword) {
      setError('Passwords do not match');
      return;
    }

    if (formData.password.length < 6) {
      setError('Password must be at least 6 characters long');
      return;
    }

    try {
      console.log('Calling apiService.register...');
      const response = await apiService.register({
        username: formData.username,
        email: formData.email,
        password: formData.password
      });
      console.log('Registration response:', response);

      if (response.success && response.data) {
        console.log('Registration successful, attempting auto-login...');
        // Registration successful, automatically log in the user
        const loginResult = await login(formData.email, formData.password);
        console.log('Auto-login result:', loginResult);
        
        if (!loginResult.success) {
          setSuccess('Registration successful! Please log in.');
          setTabValue(0); // Switch to login tab
          setFormData({ email: formData.email, password: '', username: '', confirmPassword: '' });
        }
      } else {
        console.error('Registration failed:', response);
        setError(response.error || 'Registration failed');
      }
    } catch (error) {
      console.error('Registration exception:', error);
      setError('Registration failed. Please try again.');
    }
  };

  return (
    <Paper elevation={3} sx={{ maxWidth: 400, mx: 'auto', mt: 8 }}>
      <Tabs
        value={tabValue}
        onChange={handleTabChange}
        variant="fullWidth"
        sx={{ borderBottom: 1, borderColor: 'divider' }}
      >
        <Tab label="Login" id="auth-tab-0" />
        <Tab label="Register" id="auth-tab-1" />
      </Tabs>

      {/* Login Tab */}
      <TabPanel value={tabValue} index={0}>
        <Typography variant="h5" gutterBottom align="center">
          Welcome Back
        </Typography>
        <Typography variant="body2" color="text.secondary" align="center" sx={{ mb: 3 }}>
          Sign in to access your secure chats
        </Typography>

        {error && <Alert severity="error" sx={{ mb: 2 }}>{error}</Alert>}
        {success && <Alert severity="success" sx={{ mb: 2 }}>{success}</Alert>}

        <Box component="form" onSubmit={handleLogin}>
          <TextField
            fullWidth
            label="Email"
            name="email"
            type="email"
            value={formData.email}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="email"
          />
          <TextField
            fullWidth
            label="Password"
            name="password"
            type="password"
            value={formData.password}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="current-password"
          />
          <Button
            type="submit"
            fullWidth
            variant="contained"
            sx={{ mt: 3, mb: 2 }}
            disabled={loading}
            startIcon={loading && <CircularProgress size={20} />}
          >
            {loading ? 'Signing In...' : 'Sign In'}
          </Button>
        </Box>
      </TabPanel>

      {/* Register Tab */}
      <TabPanel value={tabValue} index={1}>
        <Typography variant="h5" gutterBottom align="center">
          Create Account
        </Typography>
        <Typography variant="body2" color="text.secondary" align="center" sx={{ mb: 3 }}>
          Join the secure messaging platform
        </Typography>

        {error && <Alert severity="error" sx={{ mb: 2 }}>{error}</Alert>}

        <Box component="form" onSubmit={handleRegister}>
          <TextField
            fullWidth
            label="Username"
            name="username"
            value={formData.username}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="username"
          />
          <TextField
            fullWidth
            label="Email"
            name="email"
            type="email"
            value={formData.email}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="email"
          />
          <TextField
            fullWidth
            label="Password"
            name="password"
            type="password"
            value={formData.password}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="new-password"
            helperText="Minimum 6 characters"
          />
          <TextField
            fullWidth
            label="Confirm Password"
            name="confirmPassword"
            type="password"
            value={formData.confirmPassword}
            onChange={handleInputChange}
            margin="normal"
            required
            autoComplete="new-password"
          />
          <Button
            type="submit"
            fullWidth
            variant="contained"
            sx={{ mt: 3, mb: 2 }}
            disabled={loading}
            startIcon={loading && <CircularProgress size={20} />}
          >
            {loading ? 'Creating Account...' : 'Create Account'}
          </Button>
        </Box>
      </TabPanel>

      <Box sx={{ p: 2, textAlign: 'center' }}>
        <Typography variant="caption" color="text.secondary">
          🔒 All messages are end-to-end encrypted
        </Typography>
        <Box sx={{ mt: 2 }}>
          <Button 
            size="small" 
            variant="text" 
            onClick={() => {
              console.log('=== Debug Info ===');
              console.log('API URL:', import.meta.env.VITE_API_URL);
              console.log('WS URL:', import.meta.env.VITE_WS_URL);
              console.log('Auth token:', localStorage.getItem('authToken'));
              fetch('http://localhost:3000/api/health')
                .then(r => r.json())
                .then(d => console.log('Health check:', d))
                .catch(e => console.error('Health check failed:', e));
            }}
          >
            Debug Info
          </Button>
        </Box>
      </Box>
    </Paper>
  );
};

export default AuthForm;