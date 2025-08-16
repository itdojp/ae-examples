import { createSlice, PayloadAction } from '@reduxjs/toolkit'

export interface SecuritySettings {
  autoLockTimeout: number // in minutes
  requireBiometric: boolean
  showTypingIndicator: boolean
  showReadReceipts: boolean
  allowScreenshots: boolean
  deleteMessagesAfter: number // in days, 0 = never
}

export interface NotificationSettings {
  enabled: boolean
  sound: boolean
  vibration: boolean
  showPreview: boolean
  mutedConversations: string[]
}

export interface AppearanceSettings {
  theme: 'light' | 'dark' | 'auto'
  fontSize: 'small' | 'medium' | 'large'
  chatWallpaper: string | null
  compactMode: boolean
}

export interface PrivacySettings {
  lastSeenPrivacy: 'everyone' | 'contacts' | 'nobody'
  profilePhotoPrivacy: 'everyone' | 'contacts' | 'nobody'
  blockList: string[]
  allowNewContacts: boolean
}

export interface SettingsState {
  security: SecuritySettings
  notifications: NotificationSettings
  appearance: AppearanceSettings
  privacy: PrivacySettings
  language: string
  dataUsage: {
    autoDownloadImages: boolean
    autoDownloadVideos: boolean
    autoDownloadDocuments: boolean
    compressImages: boolean
  }
  backup: {
    enabled: boolean
    frequency: 'daily' | 'weekly' | 'monthly'
    includeMedia: boolean
    lastBackup: number | null
  }
}

const initialState: SettingsState = {
  security: {
    autoLockTimeout: 15,
    requireBiometric: false,
    showTypingIndicator: true,
    showReadReceipts: true,
    allowScreenshots: false,
    deleteMessagesAfter: 0,
  },
  notifications: {
    enabled: true,
    sound: true,
    vibration: true,
    showPreview: true,
    mutedConversations: [],
  },
  appearance: {
    theme: 'dark',
    fontSize: 'medium',
    chatWallpaper: null,
    compactMode: false,
  },
  privacy: {
    lastSeenPrivacy: 'contacts',
    profilePhotoPrivacy: 'contacts',
    blockList: [],
    allowNewContacts: true,
  },
  language: 'en',
  dataUsage: {
    autoDownloadImages: true,
    autoDownloadVideos: false,
    autoDownloadDocuments: false,
    compressImages: true,
  },
  backup: {
    enabled: false,
    frequency: 'weekly',
    includeMedia: false,
    lastBackup: null,
  },
}

const settingsSlice = createSlice({
  name: 'settings',
  initialState,
  reducers: {
    updateSecuritySettings: (state, action: PayloadAction<Partial<SecuritySettings>>) => {
      state.security = { ...state.security, ...action.payload }
    },
    
    updateNotificationSettings: (state, action: PayloadAction<Partial<NotificationSettings>>) => {
      state.notifications = { ...state.notifications, ...action.payload }
    },
    
    updateAppearanceSettings: (state, action: PayloadAction<Partial<AppearanceSettings>>) => {
      state.appearance = { ...state.appearance, ...action.payload }
    },
    
    updatePrivacySettings: (state, action: PayloadAction<Partial<PrivacySettings>>) => {
      state.privacy = { ...state.privacy, ...action.payload }
    },
    
    setLanguage: (state, action: PayloadAction<string>) => {
      state.language = action.payload
    },
    
    updateDataUsageSettings: (state, action: PayloadAction<Partial<SettingsState['dataUsage']>>) => {
      state.dataUsage = { ...state.dataUsage, ...action.payload }
    },
    
    updateBackupSettings: (state, action: PayloadAction<Partial<SettingsState['backup']>>) => {
      state.backup = { ...state.backup, ...action.payload }
    },
    
    addToBlockList: (state, action: PayloadAction<string>) => {
      if (!state.privacy.blockList.includes(action.payload)) {
        state.privacy.blockList.push(action.payload)
      }
    },
    
    removeFromBlockList: (state, action: PayloadAction<string>) => {
      state.privacy.blockList = state.privacy.blockList.filter(id => id !== action.payload)
    },
    
    muteConversation: (state, action: PayloadAction<string>) => {
      if (!state.notifications.mutedConversations.includes(action.payload)) {
        state.notifications.mutedConversations.push(action.payload)
      }
    },
    
    unmuteConversation: (state, action: PayloadAction<string>) => {
      state.notifications.mutedConversations = state.notifications.mutedConversations
        .filter(id => id !== action.payload)
    },
    
    resetToDefaults: (state) => {
      return { ...initialState }
    },
    
    loadFromStorage: (state) => {
      const savedSettings = localStorage.getItem('app_settings')
      if (savedSettings) {
        try {
          const parsed = JSON.parse(savedSettings)
          return { ...state, ...parsed }
        } catch (error) {
          console.error('Failed to load settings from storage:', error)
        }
      }
      return state
    },
    
    saveToStorage: (state) => {
      try {
        localStorage.setItem('app_settings', JSON.stringify(state))
      } catch (error) {
        console.error('Failed to save settings to storage:', error)
      }
    },
  },
})

export const {
  updateSecuritySettings,
  updateNotificationSettings,
  updateAppearanceSettings,
  updatePrivacySettings,
  setLanguage,
  updateDataUsageSettings,
  updateBackupSettings,
  addToBlockList,
  removeFromBlockList,
  muteConversation,
  unmuteConversation,
  resetToDefaults,
  loadFromStorage,
  saveToStorage,
} = settingsSlice.actions

export default settingsSlice.reducer