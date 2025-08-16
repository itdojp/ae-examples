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
  LinearProgress,
  Checkbox,
  FormControlLabel,
  Divider,
} from '@mui/material'
import {
  Visibility,
  VisibilityOff,
  Security,
  Person,
  Email,
  VpnKey,
} from '@mui/icons-material'
import { useForm } from 'react-hook-form'
import { zodResolver } from '@hookform/resolvers/zod'
import { z } from 'zod'
import { Link as RouterLink, useNavigate } from 'react-router-dom'
import { useAppDispatch, useAppSelector } from '../hooks/redux'
import { register as registerUser, clearError } from '../store/slices/authSlice'
import { EncryptionService } from '../services/encryptionService'

const registerSchema = z.object({
  displayName: z.string().min(2, 'Display name must be at least 2 characters').max(50, 'Display name must be less than 50 characters'),
  email: z.string().email('Invalid email address'),
  password: z.string()
    .min(12, 'Password must be at least 12 characters')
    .regex(/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]/, 
      'Password must contain uppercase, lowercase, number and special character'),
  confirmPassword: z.string(),
  agreeToTerms: z.boolean().refine(val => val === true, 'You must agree to the terms and conditions'),
  agreeToPrivacy: z.boolean().refine(val => val === true, 'You must agree to the privacy policy'),
}).refine((data) => data.password === data.confirmPassword, {
  message: "Passwords don't match",
  path: ["confirmPassword"],
})

type RegisterFormData = z.infer<typeof registerSchema>

const RegisterPage: React.FC = () => {
  const [showPassword, setShowPassword] = useState(false)
  const [showConfirmPassword, setShowConfirmPassword] = useState(false)
  const [passwordStrength, setPasswordStrength] = useState(0)
  const [isGeneratingKeys, setIsGeneratingKeys] = useState(false)
  
  const dispatch = useAppDispatch()
  const navigate = useNavigate()
  const { isLoading, error, isAuthenticated } = useAppSelector((state) => state.auth)

  const {
    register,
    handleSubmit,
    formState: { errors },
    watch,
    setValue,
  } = useForm<RegisterFormData>({
    resolver: zodResolver(registerSchema),
    defaultValues: {
      agreeToTerms: false,
      agreeToPrivacy: false,
    },
  })

  const password = watch('password')

  useEffect(() => {
    if (isAuthenticated) {
      navigate('/chat')
    }
  }, [isAuthenticated, navigate])

  useEffect(() => {
    dispatch(clearError())
  }, [dispatch])

  useEffect(() => {
    // Calculate password strength
    if (password) {
      let strength = 0
      if (password.length >= 8) strength += 20
      if (password.length >= 12) strength += 20
      if (/[a-z]/.test(password)) strength += 20
      if (/[A-Z]/.test(password)) strength += 20
      if (/\d/.test(password)) strength += 10
      if (/[@$!%*?&]/.test(password)) strength += 10
      setPasswordStrength(strength)
    } else {
      setPasswordStrength(0)
    }
  }, [password])

  const getPasswordStrengthColor = (strength: number): string => {
    if (strength < 40) return 'error'
    if (strength < 70) return 'warning'
    return 'success'
  }

  const getPasswordStrengthText = (strength: number): string => {
    if (strength < 40) return 'Weak'
    if (strength < 70) return 'Medium'
    return 'Strong'
  }

  const onSubmit = async (data: RegisterFormData) => {
    try {
      setIsGeneratingKeys(true)
      
      // Generate encryption keys
      const encryptionService = new EncryptionService()
      await encryptionService.initialize('temp-user-id')
      const keyPair = await encryptionService.getIdentityKeyPair()
      
      if (!keyPair) {
        throw new Error('Failed to generate encryption keys')
      }

      // Convert public key to base64 for storage
      const publicKeyArray = new Uint8Array(keyPair.publicKey)
      const publicKeyBase64 = btoa(String.fromCharCode(...publicKeyArray))

      const result = await dispatch(registerUser({
        displayName: data.displayName,
        email: data.email,
        password: data.password,
        publicKey: publicKeyBase64,
      }))

      if (result.type.endsWith('/fulfilled')) {
        // Registration successful
        navigate('/chat')
      }
    } catch (error) {
      console.error('Registration error:', error)
    } finally {
      setIsGeneratingKeys(false)
    }
  }

  const handleTogglePasswordVisibility = () => {
    setShowPassword(!showPassword)
  }

  const handleToggleConfirmPasswordVisibility = () => {
    setShowConfirmPassword(!showConfirmPassword)
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
          maxWidth: 500,
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
              Join SecureChat
            </Typography>
            <Typography variant="body2" color="text.secondary">
              Create your encrypted messaging account
            </Typography>
          </Box>

          {/* Error Alert */}
          {error && (
            <Alert severity="error" sx={{ mb: 3 }}>
              {error}
            </Alert>
          )}

          {/* Key Generation Progress */}
          {isGeneratingKeys && (
            <Alert severity="info" sx={{ mb: 3 }}>
              <Box sx={{ display: 'flex', alignItems: 'center', gap: 2 }}>
                <VpnKey />
                <Box sx={{ flex: 1 }}>
                  <Typography variant="body2">
                    Generating encryption keys...
                  </Typography>
                  <LinearProgress sx={{ mt: 1 }} />
                </Box>
              </Box>
            </Alert>
          )}

          {/* Registration Form */}
          <Box component="form" onSubmit={handleSubmit(onSubmit)}>
            <TextField
              {...register('displayName')}
              fullWidth
              label="Display Name"
              type="text"
              autoComplete="name"
              error={!!errors.displayName}
              helperText={errors.displayName?.message}
              sx={{ mb: 2 }}
              InputProps={{
                startAdornment: (
                  <InputAdornment position="start">
                    <Person />
                  </InputAdornment>
                ),
              }}
            />

            <TextField
              {...register('email')}
              fullWidth
              label="Email Address"
              type="email"
              autoComplete="email"
              error={!!errors.email}
              helperText={errors.email?.message}
              sx={{ mb: 2 }}
              InputProps={{
                startAdornment: (
                  <InputAdornment position="start">
                    <Email />
                  </InputAdornment>
                ),
              }}
            />

            <TextField
              {...register('password')}
              fullWidth
              label="Password"
              type={showPassword ? 'text' : 'password'}
              autoComplete="new-password"
              error={!!errors.password}
              helperText={errors.password?.message}
              sx={{ mb: 1 }}
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

            {/* Password Strength Indicator */}
            {password && (
              <Box sx={{ mb: 2 }}>
                <Box sx={{ display: 'flex', justifyContent: 'space-between', mb: 1 }}>
                  <Typography variant="caption" color="text.secondary">
                    Password Strength
                  </Typography>
                  <Typography 
                    variant="caption" 
                    color={`${getPasswordStrengthColor(passwordStrength)}.main`}
                    fontWeight="bold"
                  >
                    {getPasswordStrengthText(passwordStrength)}
                  </Typography>
                </Box>
                <LinearProgress
                  variant="determinate"
                  value={passwordStrength}
                  color={getPasswordStrengthColor(passwordStrength) as any}
                  sx={{ height: 6, borderRadius: 3 }}
                />
              </Box>
            )}

            <TextField
              {...register('confirmPassword')}
              fullWidth
              label="Confirm Password"
              type={showConfirmPassword ? 'text' : 'password'}
              autoComplete="new-password"
              error={!!errors.confirmPassword}
              helperText={errors.confirmPassword?.message}
              sx={{ mb: 3 }}
              InputProps={{
                endAdornment: (
                  <InputAdornment position="end">
                    <IconButton
                      onClick={handleToggleConfirmPasswordVisibility}
                      edge="end"
                    >
                      {showConfirmPassword ? <VisibilityOff /> : <Visibility />}
                    </IconButton>
                  </InputAdornment>
                ),
              }}
            />

            {/* Terms and Privacy */}
            <Box sx={{ mb: 3 }}>
              <FormControlLabel
                control={
                  <Checkbox
                    {...register('agreeToTerms')}
                    color="primary"
                  />
                }
                label={
                  <Typography variant="body2">
                    I agree to the{' '}
                    <Link href="/terms" target="_blank" underline="hover">
                      Terms of Service
                    </Link>
                  </Typography>
                }
              />
              {errors.agreeToTerms && (
                <Typography variant="caption" color="error.main" display="block" sx={{ ml: 4 }}>
                  {errors.agreeToTerms.message}
                </Typography>
              )}

              <FormControlLabel
                control={
                  <Checkbox
                    {...register('agreeToPrivacy')}
                    color="primary"
                  />
                }
                label={
                  <Typography variant="body2">
                    I agree to the{' '}
                    <Link href="/privacy" target="_blank" underline="hover">
                      Privacy Policy
                    </Link>
                  </Typography>
                }
              />
              {errors.agreeToPrivacy && (
                <Typography variant="caption" color="error.main" display="block" sx={{ ml: 4 }}>
                  {errors.agreeToPrivacy.message}
                </Typography>
              )}
            </Box>

            {/* Register Button */}
            <Button
              type="submit"
              fullWidth
              variant="contained"
              size="large"
              disabled={isLoading || isGeneratingKeys}
              sx={{
                mb: 2,
                py: 1.5,
                fontSize: '1.1rem',
                fontWeight: 'bold',
              }}
            >
              {isLoading || isGeneratingKeys ? 'Creating Account...' : 'Create Account'}
            </Button>

            {/* Divider */}
            <Divider sx={{ my: 3 }}>
              <Typography variant="body2" color="text.secondary">
                Already have an account?
              </Typography>
            </Divider>

            {/* Login Link */}
            <Button
              component={RouterLink}
              to="/login"
              fullWidth
              variant="outlined"
              size="large"
              sx={{
                py: 1.5,
                fontSize: '1.1rem',
                fontWeight: 'bold',
              }}
            >
              Sign In
            </Button>
          </Box>

          {/* Security Notice */}
          <Box sx={{ mt: 4, p: 2, bgcolor: 'grey.50', borderRadius: 2 }}>
            <Typography variant="caption" color="text.secondary" align="center" display="block">
              🔐 We'll generate unique encryption keys for your account. Keep your password safe - 
              we cannot recover it if lost.
            </Typography>
          </Box>
        </CardContent>
      </Card>
    </Box>
  )
}

export default RegisterPage