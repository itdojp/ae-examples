import React from 'react'
import { Box, CircularProgress, Typography } from '@mui/material'
import { Security } from '@mui/icons-material'

const LoadingScreen: React.FC = () => {
  return (
    <Box
      sx={{
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        minHeight: '100vh',
        background: 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
      }}
    >
      <Security sx={{ fontSize: 64, color: 'white', mb: 3 }} />
      <CircularProgress size={60} sx={{ color: 'white', mb: 3 }} />
      <Typography variant="h5" color="white" gutterBottom>
        SecureChat
      </Typography>
      <Typography variant="body1" color="white" sx={{ opacity: 0.8 }}>
        Loading secure environment...
      </Typography>
    </Box>
  )
}

export default LoadingScreen