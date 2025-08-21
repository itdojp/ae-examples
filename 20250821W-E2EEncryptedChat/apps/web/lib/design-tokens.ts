// デザイントークン定義
export const designTokens = {
  // カラーパレット
  colors: {
    // プライマリカラー（セキュリティテーマ）
    primary: {
      50: '#eff6ff',
      100: '#dbeafe', 
      200: '#bfdbfe',
      300: '#93c5fd',
      400: '#60a5fa',
      500: '#3b82f6', // メインブルー
      600: '#2563eb',
      700: '#1d4ed8',
      800: '#1e40af',
      900: '#1e3a8a',
      950: '#172554',
    },
    
    // セキュリティ状態カラー
    security: {
      // 検証済み（緑）
      verified: {
        50: '#f0fdf4',
        100: '#dcfce7',
        200: '#bbf7d0',
        300: '#86efac',
        400: '#4ade80',
        500: '#22c55e',
        600: '#16a34a',
        700: '#15803d',
        800: '#166534',
        900: '#14532d',
      },
      // 未検証（黄）
      unverified: {
        50: '#fffbeb',
        100: '#fef3c7',
        200: '#fde68a',
        300: '#fcd34d',
        400: '#fbbf24',
        500: '#f59e0b',
        600: '#d97706',
        700: '#b45309',
        800: '#92400e',
        900: '#78350f',
      },
      // 危険（赤）
      danger: {
        50: '#fef2f2',
        100: '#fee2e2',
        200: '#fecaca',
        300: '#fca5a5',
        400: '#f87171',
        500: '#ef4444',
        600: '#dc2626',
        700: '#b91c1c',
        800: '#991b1b',
        900: '#7f1d1d',
      },
      // 暗号化（紫）
      encrypted: {
        50: '#faf5ff',
        100: '#f3e8ff',
        200: '#e9d5ff',
        300: '#d8b4fe',
        400: '#c084fc',
        500: '#a855f7',
        600: '#9333ea',
        700: '#7c3aed',
        800: '#6b21a8',
        900: '#581c87',
      },
    },
    
    // グレースケール
    gray: {
      50: '#f9fafb',
      100: '#f3f4f6',
      200: '#e5e7eb',
      300: '#d1d5db',
      400: '#9ca3af',
      500: '#6b7280',
      600: '#4b5563',
      700: '#374151',
      800: '#1f2937',
      900: '#111827',
      950: '#030712',
    },
  },
  
  // タイポグラフィ
  typography: {
    fontFamily: {
      sans: ['Inter', 'ui-sans-serif', 'system-ui', 'sans-serif'],
      mono: ['JetBrains Mono', 'ui-monospace', 'monospace'],
    },
    fontSize: {
      xs: ['0.75rem', { lineHeight: '1rem' }],
      sm: ['0.875rem', { lineHeight: '1.25rem' }],
      base: ['1rem', { lineHeight: '1.5rem' }],
      lg: ['1.125rem', { lineHeight: '1.75rem' }],
      xl: ['1.25rem', { lineHeight: '1.75rem' }],
      '2xl': ['1.5rem', { lineHeight: '2rem' }],
      '3xl': ['1.875rem', { lineHeight: '2.25rem' }],
      '4xl': ['2.25rem', { lineHeight: '2.5rem' }],
    },
    fontWeight: {
      thin: '100',
      extralight: '200',
      light: '300',
      normal: '400',
      medium: '500',
      semibold: '600',
      bold: '700',
      extrabold: '800',
      black: '900',
    },
  },
  
  // スペーシング
  spacing: {
    px: '1px',
    0: '0',
    0.5: '0.125rem', // 2px
    1: '0.25rem',    // 4px
    1.5: '0.375rem', // 6px
    2: '0.5rem',     // 8px
    2.5: '0.625rem', // 10px
    3: '0.75rem',    // 12px
    3.5: '0.875rem', // 14px
    4: '1rem',       // 16px
    5: '1.25rem',    // 20px
    6: '1.5rem',     // 24px
    7: '1.75rem',    // 28px
    8: '2rem',       // 32px
    9: '2.25rem',    // 36px
    10: '2.5rem',    // 40px
    11: '2.75rem',   // 44px
    12: '3rem',      // 48px
    14: '3.5rem',    // 56px
    16: '4rem',      // 64px
    20: '5rem',      // 80px
    24: '6rem',      // 96px
    28: '7rem',      // 112px
    32: '8rem',      // 128px
    36: '9rem',      // 144px
    40: '10rem',     // 160px
    44: '11rem',     // 176px
    48: '12rem',     // 192px
    52: '13rem',     // 208px
    56: '14rem',     // 224px
    60: '15rem',     // 240px
    64: '16rem',     // 256px
    72: '18rem',     // 288px
    80: '20rem',     // 320px
    96: '24rem',     // 384px
  },
  
  // ボーダー半径
  borderRadius: {
    none: '0',
    sm: '0.125rem',   // 2px
    DEFAULT: '0.25rem', // 4px
    md: '0.375rem',   // 6px
    lg: '0.5rem',     // 8px
    xl: '0.75rem',    // 12px
    '2xl': '1rem',    // 16px
    '3xl': '1.5rem',  // 24px
    full: '9999px',
  },
  
  // シャドウ
  boxShadow: {
    sm: '0 1px 2px 0 rgb(0 0 0 / 0.05)',
    DEFAULT: '0 1px 3px 0 rgb(0 0 0 / 0.1), 0 1px 2px -1px rgb(0 0 0 / 0.1)',
    md: '0 4px 6px -1px rgb(0 0 0 / 0.1), 0 2px 4px -2px rgb(0 0 0 / 0.1)',
    lg: '0 10px 15px -3px rgb(0 0 0 / 0.1), 0 4px 6px -4px rgb(0 0 0 / 0.1)',
    xl: '0 20px 25px -5px rgb(0 0 0 / 0.1), 0 8px 10px -6px rgb(0 0 0 / 0.1)',
    '2xl': '0 25px 50px -12px rgb(0 0 0 / 0.25)',
    inner: 'inset 0 2px 4px 0 rgb(0 0 0 / 0.05)',
    none: 'none',
    // セキュリティ要素専用シャドウ
    security: '0 4px 12px -2px rgb(34 197 94 / 0.2), 0 2px 4px -1px rgb(34 197 94 / 0.1)',
    danger: '0 4px 12px -2px rgb(239 68 68 / 0.2), 0 2px 4px -1px rgb(239 68 68 / 0.1)',
    encrypted: '0 4px 12px -2px rgb(168 85 247 / 0.2), 0 2px 4px -1px rgb(168 85 247 / 0.1)',
  },
  
  // アニメーション
  animation: {
    // セキュリティ関連のアニメーション
    'pulse-security': 'pulse-security 2s cubic-bezier(0.4, 0, 0.6, 1) infinite',
    'fade-in': 'fade-in 0.2s ease-out',
    'fade-out': 'fade-out 0.2s ease-in',
    'slide-in': 'slide-in 0.3s ease-out',
    'slide-out': 'slide-out 0.3s ease-in',
    'scale-in': 'scale-in 0.2s ease-out',
    'scale-out': 'scale-out 0.2s ease-in',
  },
  
  // トランジション
  transitionDuration: {
    75: '75ms',
    100: '100ms',
    150: '150ms',
    200: '200ms',
    300: '300ms',
    500: '500ms',
    700: '700ms',
    1000: '1000ms',
  },
  
  // ブレークポイント
  screens: {
    sm: '640px',
    md: '768px',
    lg: '1024px',
    xl: '1280px',
    '2xl': '1536px',
  },
  
  // Z-index階層
  zIndex: {
    0: '0',
    10: '10',
    20: '20',
    30: '30',
    40: '40',
    50: '50', // ドロップダウン、ポップオーバー
    60: '60', // モーダルオーバーレイ
    70: '70', // モーダルコンテンツ
    80: '80', // トースト通知
    90: '90', // 最優先UI要素
    100: '100', // デバッグ・開発ツール
  },
};

// アクセシビリティ関連のトークン
export const accessibilityTokens = {
  // フォーカスリング
  focusRing: {
    width: '2px',
    color: designTokens.colors.primary[500],
    offset: '2px',
    style: 'solid',
  },
  
  // 最小タップ/クリック領域
  minTouchTarget: '44px', // WCAG AA準拠
  
  // コントラスト比（WCAG AA準拠）
  contrastRatio: {
    normal: 4.5,
    large: 3.0,
    enhanced: 7.0, // AAA準拠
  },
  
  // アニメーション設定（reducedMotionを尊重）
  reducedMotion: {
    duration: '0.01ms',
    timingFunction: 'linear',
  },
};

// セキュリティ関連のトークン
export const securityTokens = {
  // セキュリティレベルカラー
  securityLevel: {
    low: designTokens.colors.gray[400],
    medium: designTokens.colors.security.unverified[500],
    high: designTokens.colors.security.verified[500],
    critical: designTokens.colors.security.danger[500],
  },
  
  // 暗号化状態のインジケーター
  encryptionStatus: {
    encrypted: designTokens.colors.security.encrypted[500],
    unencrypted: designTokens.colors.gray[400],
    verified: designTokens.colors.security.verified[500],
    unverified: designTokens.colors.security.unverified[500],
  },
  
  // セキュリティバッジ
  badge: {
    padding: '0.25rem 0.5rem',
    borderRadius: designTokens.borderRadius.full,
    fontSize: designTokens.typography.fontSize.xs[0],
    fontWeight: designTokens.typography.fontWeight.medium,
  },
};

// ダークモード対応のトークン
export const darkModeTokens = {
  colors: {
    // ダークモード専用カラー
    dark: {
      bg: {
        primary: designTokens.colors.gray[900],
        secondary: designTokens.colors.gray[800],
        tertiary: designTokens.colors.gray[700],
      },
      text: {
        primary: designTokens.colors.gray[100],
        secondary: designTokens.colors.gray[300],
        tertiary: designTokens.colors.gray[400],
      },
      border: {
        primary: designTokens.colors.gray[700],
        secondary: designTokens.colors.gray[600],
      },
    },
  },
  
  // ダークモードでのセキュリティカラー調整
  security: {
    verified: {
      bg: 'rgb(34 197 94 / 0.1)',
      border: 'rgb(34 197 94 / 0.2)',
      text: '#4ade80',
    },
    unverified: {
      bg: 'rgb(251 191 36 / 0.1)',
      border: 'rgb(251 191 36 / 0.2)',
      text: '#fbbf24',
    },
    danger: {
      bg: 'rgb(239 68 68 / 0.1)',
      border: 'rgb(239 68 68 / 0.2)',
      text: '#f87171',
    },
    encrypted: {
      bg: 'rgb(168 85 247 / 0.1)',
      border: 'rgb(168 85 247 / 0.2)',
      text: '#c084fc',
    },
  },
};

// エクスポートされるTailwind設定用の統合トークン
export const tailwindTokens = {
  ...designTokens,
  extend: {
    colors: {
      ...designTokens.colors,
      security: designTokens.colors.security,
    },
    fontFamily: designTokens.typography.fontFamily,
    fontSize: designTokens.typography.fontSize,
    fontWeight: designTokens.typography.fontWeight,
    spacing: designTokens.spacing,
    borderRadius: designTokens.borderRadius,
    boxShadow: designTokens.boxShadow,
    animation: designTokens.animation,
    transitionDuration: designTokens.transitionDuration,
    screens: designTokens.screens,
    zIndex: designTokens.zIndex,
  },
};

export type DesignTokens = typeof designTokens;
export type AccessibilityTokens = typeof accessibilityTokens;
export type SecurityTokens = typeof securityTokens;
export type DarkModeTokens = typeof darkModeTokens;