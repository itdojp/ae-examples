'use client';

import React, { useState, useEffect } from 'react';
import { Shield, ShieldAlert, ShieldCheck, ShieldX, RefreshCw, Info } from 'lucide-react';
import * as Tooltip from '@radix-ui/react-tooltip';
import * as Progress from '@radix-ui/react-progress';
import { useTranslations } from 'next-intl';
import { cn } from '@/lib/utils';
import { useTelemetry } from '@/hooks/use-telemetry';
import type { EncryptionStatus } from '@/types/security';

interface EncryptionStatusIndicatorProps {
  encryptionStatus: EncryptionStatus;
  onRefreshStatus?: () => Promise<void>;
  showDetails?: boolean;
  className?: string;
  size?: 'sm' | 'md' | 'lg';
}

export function EncryptionStatusIndicator({
  encryptionStatus,
  onRefreshStatus,
  showDetails = false,
  className,
  size = 'md',
}: EncryptionStatusIndicatorProps) {
  const t = useTranslations('encryption');
  const { trackUIInteraction, createSecuritySpan } = useTelemetry();
  
  const [isRefreshing, setIsRefreshing] = useState(false);
  const [keyRotationProgress, setKeyRotationProgress] = useState(0);
  const [lastChecked, setLastChecked] = useState<Date>(new Date());

  // キー回転の進捗を計算（24時間サイクル）
  useEffect(() => {
    const rotationInterval = 24 * 60 * 60 * 1000; // 24時間
    const timeSinceRotation = Date.now() - encryptionStatus.lastRotated.getTime();
    const progress = Math.min((timeSinceRotation / rotationInterval) * 100, 100);
    setKeyRotationProgress(progress);
  }, [encryptionStatus.lastRotated]);

  // 定期的なステータス更新
  useEffect(() => {
    const interval = setInterval(() => {
      setLastChecked(new Date());
    }, 30000); // 30秒毎

    return () => clearInterval(interval);
  }, []);

  const handleRefresh = async () => {
    if (!onRefreshStatus || isRefreshing) return;
    
    setIsRefreshing(true);
    trackUIInteraction('EncryptionStatusIndicator', 'refresh_status');
    
    const span = createSecuritySpan('status_refresh');
    span.setAttributes({
      'encryption.algorithm': encryptionStatus.algorithm,
      'encryption.verified': encryptionStatus.verified,
    });
    
    try {
      await onRefreshStatus();
      setLastChecked(new Date());
      span.setAttributes({ 'refresh.success': true });
    } catch (error) {
      span.recordException(error as Error);
      span.setAttributes({ 'refresh.success': false });
    } finally {
      span.end();
      setIsRefreshing(false);
    }
  };

  // ステータス別のアイコンとスタイル
  const getStatusIcon = () => {
    const iconSize = size === 'sm' ? 'h-3 w-3' : size === 'lg' ? 'h-5 w-5' : 'h-4 w-4';
    
    if (!encryptionStatus.isEncrypted) {
      return <ShieldX className={cn(iconSize, 'text-red-500')} />;
    }
    
    if (encryptionStatus.verified) {
      return <ShieldCheck className={cn(iconSize, 'text-green-500')} />;
    }
    
    if (keyRotationProgress > 90) {
      return <ShieldAlert className={cn(iconSize, 'text-yellow-500')} />;
    }
    
    return <Shield className={cn(iconSize, 'text-blue-500')} />;
  };

  const getStatusColor = () => {
    if (!encryptionStatus.isEncrypted) return 'border-red-200 bg-red-50 dark:border-red-800 dark:bg-red-900/20';
    if (encryptionStatus.verified) return 'border-green-200 bg-green-50 dark:border-green-800 dark:bg-green-900/20';
    if (keyRotationProgress > 90) return 'border-yellow-200 bg-yellow-50 dark:border-yellow-800 dark:bg-yellow-900/20';
    return 'border-blue-200 bg-blue-50 dark:border-blue-800 dark:bg-blue-900/20';
  };

  const getStatusText = () => {
    if (!encryptionStatus.isEncrypted) {
      return t('not_encrypted');
    }
    
    if (encryptionStatus.verified) {
      return t('encrypted_verified', { algorithm: encryptionStatus.algorithm });
    }
    
    return t('encrypted_unverified', { algorithm: encryptionStatus.algorithm });
  };

  const getDetailedTooltip = () => {
    return (
      <div className="max-w-xs space-y-2">
        <div className="font-semibold">{t('encryption_details')}</div>
        <div className="text-sm space-y-1">
          <div>
            <span className="font-medium">{t('algorithm')}:</span> {encryptionStatus.algorithm}
          </div>
          <div>
            <span className="font-medium">{t('key_id')}:</span> {encryptionStatus.keyId.slice(0, 8)}...
          </div>
          <div>
            <span className="font-medium">{t('last_rotated')}:</span>{' '}
            {encryptionStatus.lastRotated.toLocaleDateString()}
          </div>
          <div>
            <span className="font-medium">{t('verified')}:</span>{' '}
            {encryptionStatus.verified ? t('yes') : t('no')}
          </div>
          {keyRotationProgress > 80 && (
            <div className="text-yellow-600 dark:text-yellow-400">
              {t('key_rotation_due')}
            </div>
          )}
        </div>
      </div>
    );
  };

  return (
    <Tooltip.Provider>
      <Tooltip.Root>
        <Tooltip.Trigger asChild>
          <div
            className={cn(
              'inline-flex items-center gap-2 rounded-lg border px-3 py-2',
              'transition-colors duration-200 cursor-help',
              getStatusColor(),
              size === 'sm' && 'px-2 py-1 text-sm',
              size === 'lg' && 'px-4 py-3 text-lg',
              className
            )}
            role="status"
            aria-label={getStatusText()}
          >
            {getStatusIcon()}
            
            <span className={cn(
              'font-medium',
              size === 'sm' && 'text-xs',
              size === 'lg' && 'text-base'
            )}>
              {getStatusText()}
            </span>

            {showDetails && (
              <>
                <div className="text-gray-400 dark:text-gray-500">|</div>
                <div className="flex items-center gap-1">
                  <Info className={cn(
                    'text-gray-500',
                    size === 'sm' ? 'h-3 w-3' : 'h-4 w-4'
                  )} />
                </div>
              </>
            )}
            
            {onRefreshStatus && (
              <button
                onClick={handleRefresh}
                disabled={isRefreshing}
                className={cn(
                  'ml-1 p-1 rounded hover:bg-white/50 dark:hover:bg-black/20',
                  'transition-colors duration-200 focus:outline-none focus:ring-2 focus:ring-blue-500',
                  'disabled:opacity-50 disabled:cursor-not-allowed'
                )}
                aria-label={t('refresh_status')}
              >
                <RefreshCw className={cn(
                  'text-gray-500',
                  isRefreshing && 'animate-spin',
                  size === 'sm' ? 'h-3 w-3' : 'h-4 w-4'
                )} />
              </button>
            )}
          </div>
        </Tooltip.Trigger>
        
        <Tooltip.Portal>
          <Tooltip.Content
            className={cn(
              'z-50 rounded-lg border border-gray-200 bg-white p-3 text-sm shadow-lg',
              'dark:border-gray-700 dark:bg-gray-800 dark:text-gray-100',
              'animate-in fade-in-0 zoom-in-95 data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=closed]:zoom-out-95'
            )}
            sideOffset={5}
          >
            {getDetailedTooltip()}
            <Tooltip.Arrow className="fill-white dark:fill-gray-800" />
          </Tooltip.Content>
        </Tooltip.Portal>
      </Tooltip.Root>

      {/* キー回転進捗バー */}
      {showDetails && keyRotationProgress > 50 && (
        <div className="mt-2 space-y-1">
          <div className="flex justify-between text-xs text-gray-600 dark:text-gray-400">
            <span>{t('key_rotation_progress')}</span>
            <span>{Math.round(keyRotationProgress)}%</span>
          </div>
          <Progress.Root
            className="relative h-2 w-full overflow-hidden rounded-full bg-gray-200 dark:bg-gray-700"
            value={keyRotationProgress}
          >
            <Progress.Indicator
              className={cn(
                'h-full w-full flex-1 transition-all duration-300',
                keyRotationProgress > 90 ? 'bg-red-500' : 'bg-blue-500'
              )}
              style={{ transform: `translateX(-${100 - keyRotationProgress}%)` }}
            />
          </Progress.Root>
        </div>
      )}

      {/* 最終チェック時刻 */}
      {showDetails && (
        <div className="mt-2 text-xs text-gray-500 dark:text-gray-400">
          {t('last_checked')}: {lastChecked.toLocaleTimeString()}
        </div>
      )}
    </Tooltip.Provider>
  );
}