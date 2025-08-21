'use client';

import { useCallback, useEffect, useRef } from 'react';
import { securityMetrics, SECURITY_ATTRIBUTES, trackSecurityError } from '@/lib/telemetry-config';

export function useTelemetry() {
  const activeSpans = useRef<Map<string, any>>(new Map());

  const startEncryptionSpan = useCallback((operationType: 'encrypt' | 'decrypt') => {
    const span = securityMetrics.createSecuritySpan(`message_${operationType}`);
    const spanId = `${operationType}_${Date.now()}`;
    activeSpans.current.set(spanId, span);
    return spanId;
  }, []);

  const endEncryptionSpan = useCallback((spanId: string, latency: number, success: boolean, algorithm: string = 'AES-256') => {
    const span = activeSpans.current.get(spanId);
    if (span) {
      span.setAttributes({
        [SECURITY_ATTRIBUTES.ENCRYPTION_ALGORITHM]: algorithm,
        'encryption.latency': latency,
        'encryption.success': success,
      });
      
      if (!success) {
        const error = new Error('Encryption operation failed');
        span.recordException(error);
        trackSecurityError(error, { operation: spanId.split('_')[0], latency });
      }
      
      // メトリクスの記録
      securityMetrics.recordEncryptionOperation(
        spanId.startsWith('encrypt') ? 'encrypt' : 'decrypt',
        algorithm,
        latency,
        success
      );
      
      span.end();
      activeSpans.current.delete(spanId);
    }
  }, []);

  const trackMessageSent = useCallback((encrypted: boolean, algorithm: string, verified: boolean = false, messageSize: number = 0) => {
    securityMetrics.recordSecureMessage(encrypted, algorithm, verified, messageSize);
  }, []);

  const trackVerification = useCallback((type: 'safety_number' | 'device', success: boolean, duration: number = 0) => {
    securityMetrics.recordSecurityVerification(type, success, duration);
  }, []);

  const trackUIInteraction = useCallback((component: string, action: string, securityContext?: string) => {
    securityMetrics.recordUIInteraction(component, action, securityContext);
  }, []);

  const createSecuritySpan = useCallback((operationName: string) => {
    return securityMetrics.createSecuritySpan(operationName);
  }, []);

  const trackSecurityEvent = useCallback((
    eventType: 'key_rotation' | 'device_revoked' | 'verification_failed' | 'suspicious_activity',
    severity: 'low' | 'medium' | 'high' | 'critical',
    details?: Record<string, any>
  ) => {
    securityMetrics.recordSecurityEvent(eventType, severity, details);
  }, []);

  const trackPerformance = useCallback((metricName: string, value: number, unit: string = 'ms', context?: Record<string, string>) => {
    securityMetrics.recordPerformanceMetric(metricName, value, unit, context);
  }, []);

  const trackComplianceCheck = useCallback((checkType: 'wcag' | 'security' | 'privacy', passed: boolean, score?: number) => {
    securityMetrics.recordComplianceCheck(checkType, passed, score);
  }, []);

  // コンポーネントアンマウント時にアクティブなスパンを終了
  useEffect(() => {
    return () => {
      activeSpans.current.forEach((span) => {
        span.end();
      });
      activeSpans.current.clear();
    };
  }, []);

  return {
    startEncryptionSpan,
    endEncryptionSpan,
    trackMessageSent,
    trackVerification,
    trackUIInteraction,
    createSecuritySpan,
    trackSecurityEvent,
    trackPerformance,
    trackComplianceCheck,
  };
}