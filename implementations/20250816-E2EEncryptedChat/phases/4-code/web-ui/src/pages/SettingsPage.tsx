import React from 'react'
import { Box, Typography, Container } from '@mui/material'
import { Settings } from '@mui/icons-material'

const SettingsPage: React.FC = () => {
  return (
    <Box
      sx={{
        height: '100vh',
        display: 'flex',
        flexDirection: 'column',
        background: 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
      }}
    >
      <Container
        maxWidth="lg"
        sx={{
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          justifyContent: 'center',
          height: '100%',
          color: 'white',
        }}
      >
        <Settings sx={{ fontSize: 120, mb: 4, opacity: 0.8 }} />
        <Typography variant="h2" gutterBottom fontWeight="bold">
          Settings
        </Typography>
        <Typography variant="h5" sx={{ opacity: 0.9, mb: 4 }}>
          Security & Privacy Configuration
        </Typography>
        <Typography variant="body1" sx={{ opacity: 0.7, textAlign: 'center', maxWidth: 600 }}>
          Settings page for managing security preferences, encryption settings, and privacy controls. 
          Full settings interface will be implemented in the next development phase.
        </Typography>
      </Container>
    </Box>
  )
}

export default SettingsPage