import { v4 as uuidv4 } from 'uuid'

export interface DeviceInfo {
  id: string
  name: string
  type: 'desktop' | 'mobile' | 'tablet'
  os: string
  browser: string
  fingerprint: string
  createdAt: number
}

export function generateDeviceId(): string {
  // Check if we already have a device ID stored
  let deviceId = localStorage.getItem('device_id')
  
  if (!deviceId) {
    deviceId = uuidv4()
    localStorage.setItem('device_id', deviceId)
  }
  
  return deviceId
}

export function getDeviceInfo(): DeviceInfo {
  const deviceId = generateDeviceId()
  const userAgent = navigator.userAgent
  
  // Detect device type
  const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(userAgent)
  const isTablet = /iPad|Android(?!.*Mobile)/i.test(userAgent)
  
  let deviceType: 'desktop' | 'mobile' | 'tablet' = 'desktop'
  if (isTablet) {
    deviceType = 'tablet'
  } else if (isMobile) {
    deviceType = 'mobile'
  }

  // Detect OS
  let os = 'Unknown'
  if (userAgent.includes('Windows')) os = 'Windows'
  else if (userAgent.includes('Mac')) os = 'macOS'
  else if (userAgent.includes('Linux')) os = 'Linux'
  else if (userAgent.includes('Android')) os = 'Android'
  else if (userAgent.includes('iOS') || userAgent.includes('iPhone') || userAgent.includes('iPad')) os = 'iOS'

  // Detect browser
  let browser = 'Unknown'
  if (userAgent.includes('Chrome') && !userAgent.includes('Edg')) browser = 'Chrome'
  else if (userAgent.includes('Firefox')) browser = 'Firefox'
  else if (userAgent.includes('Safari') && !userAgent.includes('Chrome')) browser = 'Safari'
  else if (userAgent.includes('Edg')) browser = 'Edge'
  else if (userAgent.includes('Opera')) browser = 'Opera'

  // Generate device fingerprint
  const fingerprint = generateDeviceFingerprint()

  return {
    id: deviceId,
    name: `${browser} on ${os}`,
    type: deviceType,
    os,
    browser,
    fingerprint,
    createdAt: Date.now(),
  }
}

export function generateDeviceFingerprint(): string {
  const canvas = document.createElement('canvas')
  const ctx = canvas.getContext('2d')
  
  // Canvas fingerprinting
  if (ctx) {
    ctx.textBaseline = 'top'
    ctx.font = '14px Arial'
    ctx.fillText('Device fingerprint', 2, 2)
  }
  const canvasFingerprint = canvas.toDataURL()

  // Screen information
  const screen = {
    width: window.screen.width,
    height: window.screen.height,
    colorDepth: window.screen.colorDepth,
    pixelRatio: window.devicePixelRatio,
  }

  // Navigator information
  const navigator = {
    language: window.navigator.language,
    languages: window.navigator.languages?.join(',') || '',
    platform: window.navigator.platform,
    cookieEnabled: window.navigator.cookieEnabled,
    doNotTrack: window.navigator.doNotTrack,
    hardwareConcurrency: window.navigator.hardwareConcurrency,
    maxTouchPoints: window.navigator.maxTouchPoints,
  }

  // Timezone
  const timezone = Intl.DateTimeFormat().resolvedOptions().timeZone

  // Combine all data
  const fingerprintData = {
    canvas: canvasFingerprint,
    screen,
    navigator,
    timezone,
    userAgent: window.navigator.userAgent,
  }

  // Create hash of the fingerprint data
  const fingerprintString = JSON.stringify(fingerprintData)
  return btoa(fingerprintString).slice(0, 32) // Simple base64 hash, truncated
}

export function isTrustedDevice(): boolean {
  const trustedDevices = getTrustedDevices()
  const currentDeviceId = generateDeviceId()
  return trustedDevices.includes(currentDeviceId)
}

export function addTrustedDevice(deviceId?: string): void {
  const id = deviceId || generateDeviceId()
  const trustedDevices = getTrustedDevices()
  
  if (!trustedDevices.includes(id)) {
    trustedDevices.push(id)
    localStorage.setItem('trusted_devices', JSON.stringify(trustedDevices))
  }
}

export function removeTrustedDevice(deviceId: string): void {
  const trustedDevices = getTrustedDevices()
  const updatedDevices = trustedDevices.filter(id => id !== deviceId)
  localStorage.setItem('trusted_devices', JSON.stringify(updatedDevices))
}

export function getTrustedDevices(): string[] {
  const stored = localStorage.getItem('trusted_devices')
  return stored ? JSON.parse(stored) : []
}

export function clearDeviceData(): void {
  localStorage.removeItem('device_id')
  localStorage.removeItem('trusted_devices')
}

// Security utilities
export function detectSuspiciousActivity(): boolean {
  const currentFingerprint = generateDeviceFingerprint()
  const storedFingerprint = localStorage.getItem('device_fingerprint')
  
  if (storedFingerprint && storedFingerprint !== currentFingerprint) {
    // Device fingerprint changed significantly
    console.warn('Device fingerprint mismatch detected')
    return true
  }
  
  if (!storedFingerprint) {
    localStorage.setItem('device_fingerprint', currentFingerprint)
  }
  
  return false
}

export function isDeviceSupported(): boolean {
  // Check for required Web APIs
  const requiredAPIs = [
    'crypto',
    'indexedDB',
    'localStorage',
    'WebSocket',
  ]
  
  for (const api of requiredAPIs) {
    if (!(api in window)) {
      return false
    }
  }
  
  // Check for WebCrypto API
  if (!window.crypto?.subtle) {
    return false
  }
  
  return true
}

export function getDeviceCapabilities() {
  return {
    webCrypto: !!window.crypto?.subtle,
    indexedDB: !!window.indexedDB,
    localStorage: !!window.localStorage,
    webSockets: !!window.WebSocket,
    notifications: 'Notification' in window,
    serviceWorker: 'serviceWorker' in navigator,
    pushManager: 'PushManager' in window,
    webRTC: !!(window as any).RTCPeerConnection,
    mediaDevices: !!navigator.mediaDevices,
    geolocation: !!navigator.geolocation,
  }
}