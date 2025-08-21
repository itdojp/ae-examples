import { NextIntlClientProvider } from 'next-intl';
import { getLocale, getMessages } from 'next-intl/server';
import { Inter } from 'next/font/google';
import { ThemeProvider } from '@/components/providers/ThemeProvider';
import { TelemetryInitializer } from '@/components/providers/TelemetryInitializer';
import './globals.css';

const inter = Inter({ subsets: ['latin'] });

export const metadata = {
  title: 'ae-framework | Secure E2E Encrypted Chat',
  description: 'Production-ready secure end-to-end encrypted chat application with Phase 6 UI/UX automation',
  keywords: 'secure chat, encryption, e2e, privacy, messaging',
  authors: [{ name: 'ae-framework' }],
  robots: 'index, follow',
  openGraph: {
    title: 'ae-framework | Secure E2E Encrypted Chat',
    description: 'Production-ready secure end-to-end encrypted chat application',
    type: 'website',
    locale: 'en_US',
  },
  viewport: {
    width: 'device-width',
    initialScale: 1,
    maximumScale: 1,
  },
};

export default async function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  const locale = await getLocale();
  const messages = await getMessages();

  return (
    <html lang={locale} suppressHydrationWarning>
      <head>
        {/* Security headers */}
        <meta httpEquiv="X-Content-Type-Options" content="nosniff" />
        <meta httpEquiv="X-Frame-Options" content="DENY" />
        <meta httpEquiv="X-XSS-Protection" content="1; mode=block" />
        <meta name="referrer" content="strict-origin-when-cross-origin" />
        
        {/* PWA support */}
        <meta name="theme-color" content="#3b82f6" />
        <meta name="apple-mobile-web-app-capable" content="yes" />
        <meta name="apple-mobile-web-app-status-bar-style" content="default" />
        
        {/* Preconnect to important domains */}
        <link rel="preconnect" href="https://fonts.googleapis.com" />
        <link rel="preconnect" href="https://fonts.gstatic.com" crossOrigin="" />
      </head>
      <body className={`${inter.className} reduced-motion high-contrast`}>
        <TelemetryInitializer>
          <ThemeProvider defaultTheme="system" storageKey="ae-framework-theme">
            <NextIntlClientProvider messages={messages}>
              <div className="min-h-screen bg-white dark:bg-gray-900 text-gray-900 dark:text-gray-100">
                {children}
              </div>
            </NextIntlClientProvider>
          </ThemeProvider>
        </TelemetryInitializer>
      </body>
    </html>
  );
}