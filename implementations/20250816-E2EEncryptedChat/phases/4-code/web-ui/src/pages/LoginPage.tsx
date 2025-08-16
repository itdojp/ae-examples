import React, { useState, useEffect } from 'react'
import {
  Box,
  Card,
  CardContent,
  TextField,
  Button,
  Typography,
  Link,
  Alert,
  InputAdornment,
  IconButton,
  Switch,
  FormControlLabel,
  Divider,
} from '@mui/material'
import {
  Visibility,
  VisibilityOff,
  Security,
  PhoneAndroid,
} from '@mui/icons-material'
import { useForm } from 'react-hook-form'
import { zodResolver } from '@hookform/resolvers/zod'
import { z } from 'zod'
import { Link as RouterLink, useNavigate } from 'react-router-dom'
import { useAppDispatch, useAppSelector } from '../hooks/redux'
import { login, clearError, setDeviceId } from '../store/slices/authSlice'
import { generateDeviceId } from '../utils/deviceUtils'

const loginSchema = z.object({
  email: z.string().email('Invalid email address'),
  password: z.string().min(8, 'Password must be at least 8 characters'),
  totpCode: z.string().optional(),
  rememberDevice: z.boolean().default(false),
})

type LoginFormData = z.infer<typeof loginSchema>

const LoginPage: React.FC = () => {
  const [showPassword, setShowPassword] = useState(false)
  const [showTwoFactor, setShowTwoFactor] = useState(false)
  const [deviceId, setLocalDeviceId] = useState<string>('')
  
  const dispatch = useAppDispatch()
  const navigate = useNavigate()
  const { isLoading, error, isAuthenticated } = useAppSelector((state) => state.auth)

  const {
    register,
    handleSubmit,
    formState: { errors },
    watch,
    setValue,
  } = useForm<LoginFormData>({
    resolver: zodResolver(loginSchema),
    defaultValues: {
      rememberDevice: false,
    },
  })

  useEffect(() => {
    // Generate device ID on component mount
    const id = generateDeviceId()
    setLocalDeviceId(id)
    dispatch(setDeviceId(id))
  }, [dispatch])

  useEffect(() => {
    console.log('LoginPage: Authentication state changed:', { isAuthenticated })
    if (isAuthenticated) {
      console.log('LoginPage: Navigating to /chat')
      navigate('/chat')
    }
  }, [isAuthenticated, navigate])

  useEffect(() => {
    // Clear any previous errors when component mounts
    dispatch(clearError())
  }, [dispatch])

  const onSubmit = async (data: LoginFormData) => {
    try {
      console.log('LoginPage: Submitting login form', { email: data.email, deviceId })
      const result = await dispatch(login({
        email: data.email,
        password: data.password,
        totpCode: data.totpCode,
        deviceId,
      }))

      console.log('LoginPage: Login result:', result)

      if (result.type.endsWith('/rejected')) {
        // Check if 2FA is required
        if (result.payload === 'Two-factor authentication required') {
          setShowTwoFactor(true)
        }
      } else if (result.type.endsWith('/fulfilled')) {
        console.log('LoginPage: Login successful, payload:', result.payload)
      }
    } catch (error) {
      console.error('Login error:', error)
    }
  }

  const handleTogglePasswordVisibility = () => {
    setShowPassword(!showPassword)
  }

  return (
    <Box
      sx={{
        minHeight: '100vh',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        background: 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
        padding: 2,
      }}
    >
      <Card
        sx={{
          maxWidth: 400,
          width: '100%',
          boxShadow: '0 20px 40px rgba(0,0,0,0.1)',
          borderRadius: 3,
        }}
      >
        <CardContent sx={{ p: 4 }}>
          {/* Header */}
          <Box sx={{ textAlign: 'center', mb: 4 }}>
            <Security sx={{ fontSize: 48, color: 'primary.main', mb: 2 }} />
            <Typography variant="h4" fontWeight="bold" gutterBottom>
              SecureChat
            </Typography>
            <Typography variant="body2" color="text.secondary">
              End-to-End Encrypted Messaging
            </Typography>
          </Box>

          {/* Error Alert */}
          {error && (
            <Alert severity="error" sx={{ mb: 3 }}>
              {error}
            </Alert>
          )}

          {/* Login Form */}
          <Box component="form" onSubmit={handleSubmit(onSubmit)}>
            <TextField
              {...register('email')}
              fullWidth
              label="Email Address"
              type="email"
              autoComplete="email"
              error={!!errors.email}
              helperText={errors.email?.message}
              sx={{ mb: 2 }}
            />

            <TextField
              {...register('password')}
              fullWidth
              label="Password"
              type={showPassword ? 'text' : 'password'}
              autoComplete="current-password"
              error={!!errors.password}
              helperText={errors.password?.message}
              sx={{ mb: 2 }}
              InputProps={{
                endAdornment: (
                  <InputAdornment position="end">
                    <IconButton
                      onClick={handleTogglePasswordVisibility}
                      edge="end"
                    >
                      {showPassword ? <VisibilityOff /> : <Visibility />}
                    </IconButton>
                  </InputAdornment>
                ),
              }}
            />

            {/* Two-Factor Authentication */}
            {showTwoFactor && (
              <>
                <Divider sx={{ my: 3 }}>
                  <Typography variant="body2" color="text.secondary">
                    Two-Factor Authentication
                  </Typography>
                </Divider>

                <TextField
                  {...register('totpCode')}
                  fullWidth
                  label="Authentication Code"
                  type="text"
                  autoComplete="one-time-code"
                  error={!!errors.totpCode}
                  helperText={errors.totpCode?.message || 'Enter the 6-digit code from your authenticator app'}
                  sx={{ mb: 2 }}
                  InputProps={{
                    startAdornment: (
                      <InputAdornment position="start">
                        <PhoneAndroid />
                      </InputAdornment>
                    ),
                  }}
                />
              </>
            )}

            {/* Remember Device */}
            <FormControlLabel
              control={
                <Switch
                  {...register('rememberDevice')}
                  checked={watch('rememberDevice')}
                  onChange={(e) => setValue('rememberDevice', e.target.checked)}
                />
              }
              label="Trust this device"
              sx={{ mb: 3 }}
            />

            {/* Login Button */}
            <Button
              type="submit"
              fullWidth
              variant="contained"
              size="large"
              disabled={isLoading}
              sx={{
                mb: 2,
                py: 1.5,
                fontSize: '1.1rem',
                fontWeight: 'bold',
              }}
            >
              {isLoading ? 'Signing in...' : 'Sign In'}
            </Button>

            {/* Forgot Password */}
            <Box sx={{ textAlign: 'center', mb: 2 }}>
              <Link
                component={RouterLink}
                to="/forgot-password"
                variant="body2"
                underline="hover"
              >
                Forgot your password?
              </Link>
            </Box>

            {/* Divider */}
            <Divider sx={{ my: 3 }}>
              <Typography variant="body2" color="text.secondary">
                New to SecureChat?
              </Typography>
            </Divider>

            {/* Register Link */}
            <Button
              component={RouterLink}
              to="/register"
              fullWidth
              variant="outlined"
              size="large"
              sx={{
                py: 1.5,
                fontSize: '1.1rem',
                fontWeight: 'bold',
              }}
            >
              Create Account
            </Button>
          </Box>

          {/* Security Notice */}
          <Box sx={{ mt: 4, p: 2, bgcolor: 'grey.50', borderRadius: 2 }}>
            <Typography variant="caption" color="text.secondary" align="center" display="block">
              🔐 Your messages are end-to-end encrypted. Not even we can read them.
            </Typography>
          </Box>
        </CardContent>
      </Card>
    </Box>
  )
}

export default LoginPage