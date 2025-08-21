const { tailwindTokens } = require('./lib/design-tokens');

/** @type {import('tailwindcss').Config} */
module.exports = {
  darkMode: ['class'],
  content: [
    './app/**/*.{js,ts,jsx,tsx,mdx}',
    './components/**/*.{js,ts,jsx,tsx,mdx}',
    './lib/**/*.{js,ts,jsx,tsx}',
    './hooks/**/*.{js,ts,jsx,tsx}',
    '../../packages/ui/src/**/*.{js,ts,jsx,tsx}',
  ],
  theme: {
    extend: {
      ...tailwindTokens.extend,
      // カスタムキーフレーム
      keyframes: {
        'pulse-security': {
          '0%, 100%': { opacity: '1' },
          '50%': { opacity: '0.7' },
        },
        'fade-in': {
          '0%': { opacity: '0' },
          '100%': { opacity: '1' },
        },
        'fade-out': {
          '0%': { opacity: '1' },
          '100%': { opacity: '0' },
        },
        'slide-in': {
          '0%': { transform: 'translateY(-10px)', opacity: '0' },
          '100%': { transform: 'translateY(0)', opacity: '1' },
        },
        'slide-out': {
          '0%': { transform: 'translateY(0)', opacity: '1' },
          '100%': { transform: 'translateY(-10px)', opacity: '0' },
        },
        'scale-in': {
          '0%': { transform: 'scale(0.95)', opacity: '0' },
          '100%': { transform: 'scale(1)', opacity: '1' },
        },
        'scale-out': {
          '0%': { transform: 'scale(1)', opacity: '1' },
          '100%': { transform: 'scale(0.95)', opacity: '0' },
        },
      },
      // アクセシビリティ対応のユーティリティ
      minHeight: {
        'touch-target': '44px', // WCAG AA準拠の最小タップ領域
      },
      minWidth: {
        'touch-target': '44px',
      },
    },
  },
  plugins: [
    // カスタムプラグインでアクセシビリティユーティリティを追加
    function({ addUtilities, theme }) {
      addUtilities({
        '.focus-ring': {
          '&:focus': {
            outline: 'none',
            'box-shadow': `0 0 0 2px ${theme('colors.primary.500')}, 0 0 0 4px ${theme('colors.primary.500')}33`,
          },
        },
        '.focus-ring-danger': {
          '&:focus': {
            outline: 'none',
            'box-shadow': `0 0 0 2px ${theme('colors.security.danger.500')}, 0 0 0 4px ${theme('colors.security.danger.500')}33`,
          },
        },
        '.focus-ring-security': {
          '&:focus': {
            outline: 'none',
            'box-shadow': `0 0 0 2px ${theme('colors.security.verified.500')}, 0 0 0 4px ${theme('colors.security.verified.500')}33`,
          },
        },
        '.reduced-motion': {
          '@media (prefers-reduced-motion: reduce)': {
            'animation-duration': '0.01ms !important',
            'animation-iteration-count': '1 !important',
            'transition-duration': '0.01ms !important',
          },
        },
        '.high-contrast': {
          '@media (prefers-contrast: high)': {
            'border-width': '2px',
            'font-weight': '600',
          },
        },
      });
    },
    // セキュリティ関連のユーティリティクラス
    function({ addComponents, theme }) {
      addComponents({
        '.security-badge': {
          display: 'inline-flex',
          alignItems: 'center',
          padding: theme('spacing.1') + ' ' + theme('spacing.2'),
          borderRadius: theme('borderRadius.full'),
          fontSize: theme('fontSize.xs')[0],
          fontWeight: theme('fontWeight.medium'),
          lineHeight: theme('fontSize.xs')[1].lineHeight,
        },
        '.security-badge-verified': {
          backgroundColor: theme('colors.security.verified.100'),
          color: theme('colors.security.verified.800'),
          borderWidth: '1px',
          borderColor: theme('colors.security.verified.200'),
          '.dark &': {
            backgroundColor: 'rgb(34 197 94 / 0.1)',
            color: '#4ade80',
            borderColor: 'rgb(34 197 94 / 0.2)',
          },
        },
        '.security-badge-unverified': {
          backgroundColor: theme('colors.security.unverified.100'),
          color: theme('colors.security.unverified.800'),
          borderWidth: '1px',
          borderColor: theme('colors.security.unverified.200'),
          '.dark &': {
            backgroundColor: 'rgb(251 191 36 / 0.1)',
            color: '#fbbf24',
            borderColor: 'rgb(251 191 36 / 0.2)',
          },
        },
        '.security-badge-danger': {
          backgroundColor: theme('colors.security.danger.100'),
          color: theme('colors.security.danger.800'),
          borderWidth: '1px',
          borderColor: theme('colors.security.danger.200'),
          '.dark &': {
            backgroundColor: 'rgb(239 68 68 / 0.1)',
            color: '#f87171',
            borderColor: 'rgb(239 68 68 / 0.2)',
          },
        },
        '.security-badge-encrypted': {
          backgroundColor: theme('colors.security.encrypted.100'),
          color: theme('colors.security.encrypted.800'),
          borderWidth: '1px',
          borderColor: theme('colors.security.encrypted.200'),
          '.dark &': {
            backgroundColor: 'rgb(168 85 247 / 0.1)',
            color: '#c084fc',
            borderColor: 'rgb(168 85 247 / 0.2)',
          },
        },
      });
    },
  ],
};