'use client';

import { useEffect, ReactNode } from 'react';
import { initializeTelemetry } from '@/lib/telemetry-config';

interface TelemetryInitializerProps {
  children: ReactNode;
}

export function TelemetryInitializer({ children }: TelemetryInitializerProps) {
  useEffect(() => {
    // OpenTelemetryの初期化
    initializeTelemetry();
    
    // パフォーマンス監視の初期化
    if (typeof window !== 'undefined') {
      // Core Web Vitalsの監視
      const observeWebVitals = () => {
        // First Contentful Paint (FCP)
        const fcpObserver = new PerformanceObserver((list) => {
          for (const entry of list.getEntries()) {
            if (entry.entryType === 'paint' && entry.name === 'first-contentful-paint') {
              console.log('FCP:', entry.startTime);
              // メトリクスをOpenTelemetryに送信
            }
          }
        });
        fcpObserver.observe({ entryTypes: ['paint'] });

        // Largest Contentful Paint (LCP)
        const lcpObserver = new PerformanceObserver((list) => {
          const entries = list.getEntries();
          const lastEntry = entries[entries.length - 1];
          console.log('LCP:', lastEntry.startTime);
          // メトリクスをOpenTelemetryに送信
        });
        lcpObserver.observe({ entryTypes: ['largest-contentful-paint'] });

        // First Input Delay (FID) - 実際のユーザーインタラクション時に測定
        const fidObserver = new PerformanceObserver((list) => {
          for (const entry of list.getEntries()) {
            const fid = entry.processingStart - entry.startTime;
            console.log('FID:', fid);
            // メトリクスをOpenTelemetryに送信
          }
        });
        fidObserver.observe({ entryTypes: ['first-input'] });

        // Cumulative Layout Shift (CLS)
        let clsValue = 0;
        const clsObserver = new PerformanceObserver((list) => {
          for (const entry of list.getEntries()) {
            if (!(entry as any).hadRecentInput) {
              clsValue += (entry as any).value;
            }
          }
          console.log('CLS:', clsValue);
          // メトリクスをOpenTelemetryに送信
        });
        clsObserver.observe({ entryTypes: ['layout-shift'] });
      };

      // DOMContentLoaded後に監視を開始
      if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', observeWebVitals);
      } else {
        observeWebVitals();
      }

      // エラーハンドリング
      const handleError = (event: ErrorEvent) => {
        console.error('Application error:', event.error);
        // エラーをOpenTelemetryに送信
      };

      const handleUnhandledRejection = (event: PromiseRejectionEvent) => {
        console.error('Unhandled promise rejection:', event.reason);
        // エラーをOpenTelemetryに送信
      };

      window.addEventListener('error', handleError);
      window.addEventListener('unhandledrejection', handleUnhandledRejection);

      return () => {
        window.removeEventListener('error', handleError);
        window.removeEventListener('unhandledrejection', handleUnhandledRejection);
      };
    }
  }, []);

  return <>{children}</>;
}