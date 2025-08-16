import React, { Component, ErrorInfo, ReactNode } from 'react'
import { Box, Typography, Button, Alert } from '@mui/material'
import { Security, Refresh } from '@mui/icons-material'

interface Props {
  children: ReactNode
}

interface State {
  hasError: boolean
  error?: Error
  errorInfo?: ErrorInfo
}

class ErrorBoundary extends Component<Props, State> {
  constructor(props: Props) {
    super(props)
    this.state = { hasError: false }
  }

  static getDerivedStateFromError(error: Error): State {
    return { hasError: true, error }
  }

  componentDidCatch(error: Error, errorInfo: ErrorInfo) {
    console.error('ErrorBoundary caught an error:', error, errorInfo)
    this.setState({ error, errorInfo })
  }

  handleReload = () => {
    window.location.reload()
  }

  render() {
    if (this.state.hasError) {
      return (
        <Box
          sx={{
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            justifyContent: 'center',
            minHeight: '100vh',
            padding: 3,
            background: 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
          }}
        >
          <Box
            sx={{
              maxWidth: 600,
              width: '100%',
              backgroundColor: 'white',
              borderRadius: 3,
              padding: 4,
              textAlign: 'center',
            }}
          >
            <Security sx={{ fontSize: 64, color: 'error.main', mb: 3 }} />
            <Typography variant="h4" gutterBottom>
              Something went wrong
            </Typography>
            <Typography variant="body1" color="text.secondary" paragraph>
              We're sorry, but something unexpected happened. Your data is safe and secure.
            </Typography>
            
            {process.env.NODE_ENV === 'development' && this.state.error && (
              <Alert severity="error" sx={{ mb: 3, textAlign: 'left' }}>
                <Typography variant="body2" component="pre" sx={{ whiteSpace: 'pre-wrap' }}>
                  {this.state.error.toString()}
                </Typography>
              </Alert>
            )}
            
            <Button
              variant="contained"
              startIcon={<Refresh />}
              onClick={this.handleReload}
              size="large"
            >
              Reload Application
            </Button>
          </Box>
        </Box>
      )
    }

    return this.props.children
  }
}

export default ErrorBoundary