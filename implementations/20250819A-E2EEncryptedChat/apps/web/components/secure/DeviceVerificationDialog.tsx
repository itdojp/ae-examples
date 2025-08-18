'use client';

import React, { useState, useCallback, useEffect } from 'react';
import { Shield, ShieldCheck, ShieldAlert, Smartphone, Monitor, Tablet, AlertTriangle, Check, X, RefreshCw } from 'lucide-react';
import * as Dialog from '@radix-ui/react-dialog';
import * as AlertDialog from '@radix-ui/react-alert-dialog';
import { useTranslations } from 'next-intl';
import { cn } from '@/lib/utils';
import { useTelemetry } from '@/hooks/use-telemetry';
import type { DeviceInfo } from '@/types/security';

interface DeviceVerificationDialogProps {
  devices: DeviceInfo[];
  currentDeviceId: string;
  onVerifyDevice: (deviceId: string) => Promise<void>;
  onRevokeDevice: (deviceId: string) => Promise<void>;
  onRefreshDevices: () => Promise<void>;
  isOpen: boolean;
  onClose: () => void;
  className?: string;
}

export function DeviceVerificationDialog({
  devices,
  currentDeviceId,
  onVerifyDevice,
  onRevokeDevice,
  onRefreshDevices,
  isOpen,
  onClose,
  className,
}: DeviceVerificationDialogProps) {
  const t = useTranslations('devices');
  const { trackUIInteraction, trackVerification, createSecuritySpan } = useTelemetry();
  
  const [verifyingDevices, setVerifyingDevices] = useState<Set<string>>(new Set());
  const [revokingDevices, setRevokingDevices] = useState<Set<string>>(new Set());
  const [isRefreshing, setIsRefreshing] = useState(false);
  const [revokeConfirm, setRevokeConfirm] = useState<string | null>(null);
  const [filter, setFilter] = useState<'all' | 'verified' | 'unverified'>('all');

  // デバイス統計の計算
  const deviceStats = {
    total: devices.length,
    verified: devices.filter(d => d.verified).length,
    unverified: devices.filter(d => !d.verified).length,
    currentDevice: devices.find(d => d.id === currentDeviceId),
  };

  // フィルタリングされたデバイス一覧
  const filteredDevices = devices.filter(device => {
    switch (filter) {
      case 'verified':
        return device.verified;
      case 'unverified':
        return !device.verified;
      default:
        return true;
    }
  });

  // デバイスタイプ別アイコン
  const getDeviceIcon = (platform: string) => {
    const iconClass = "h-5 w-5";
    switch (platform.toLowerCase()) {
      case 'ios':
      case 'android':
        return <Smartphone className={iconClass} />;
      case 'windows':
      case 'macos':
      case 'linux':
        return <Monitor className={iconClass} />;
      case 'tablet':
        return <Tablet className={iconClass} />;
      default:
        return <Monitor className={iconClass} />;
    }
  };

  // デバイス検証処理
  const handleVerifyDevice = async (deviceId: string) => {
    setVerifyingDevices(prev => new Set(prev).add(deviceId));
    const span = createSecuritySpan('device_verification');
    span.setAttributes({
      'device.id': deviceId,
      'device.platform': devices.find(d => d.id === deviceId)?.platform || 'unknown',
    });
    
    try {
      await onVerifyDevice(deviceId);
      trackVerification('device', true);
      trackUIInteraction('DeviceVerificationDialog', 'verify_device_success');
      span.setAttributes({ 'verification.success': true });
    } catch (error) {
      trackVerification('device', false);
      trackUIInteraction('DeviceVerificationDialog', 'verify_device_failed');
      span.recordException(error as Error);
      span.setAttributes({ 'verification.success': false });
    } finally {
      span.end();
      setVerifyingDevices(prev => {
        const next = new Set(prev);
        next.delete(deviceId);
        return next;
      });
    }
  };

  // デバイス取り消し処理
  const handleRevokeDevice = async (deviceId: string) => {
    if (deviceId === currentDeviceId) {
      trackUIInteraction('DeviceVerificationDialog', 'revoke_current_device_attempted');
      return; // 現在のデバイスは取り消し不可
    }

    setRevokingDevices(prev => new Set(prev).add(deviceId));
    const span = createSecuritySpan('device_revocation');
    span.setAttributes({
      'device.id': deviceId,
      'device.platform': devices.find(d => d.id === deviceId)?.platform || 'unknown',
    });
    
    try {
      await onRevokeDevice(deviceId);
      trackUIInteraction('DeviceVerificationDialog', 'revoke_device_success');
      span.setAttributes({ 'revocation.success': true });
      setRevokeConfirm(null);
    } catch (error) {
      trackUIInteraction('DeviceVerificationDialog', 'revoke_device_failed');
      span.recordException(error as Error);
      span.setAttributes({ 'revocation.success': false });
    } finally {
      span.end();
      setRevokingDevices(prev => {
        const next = new Set(prev);
        next.delete(deviceId);
        return next;
      });
    }
  };

  // デバイス一覧の更新
  const handleRefresh = async () => {
    setIsRefreshing(true);
    trackUIInteraction('DeviceVerificationDialog', 'refresh_devices');
    
    try {
      await onRefreshDevices();
    } catch (error) {
      console.error('Failed to refresh devices:', error);
    } finally {
      setIsRefreshing(false);
    }
  };

  // フィンガープリントの短縮表示
  const formatFingerprint = (fingerprint: string) => {
    return fingerprint.slice(0, 8) + '...' + fingerprint.slice(-8);
  };

  return (
    <>
      <Dialog.Root open={isOpen} onOpenChange={onClose}>
        <Dialog.Portal>
          <Dialog.Overlay className="fixed inset-0 z-50 bg-black/50 backdrop-blur-sm data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0" />
          <Dialog.Content className={cn(
            'fixed left-[50%] top-[50%] z-50 grid w-full max-w-2xl translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200',
            'data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0 data-[state=closed]:zoom-out-95 data-[state=open]:zoom-in-95',
            'rounded-lg border-gray-200 bg-white dark:border-gray-700 dark:bg-gray-800 max-h-[90vh] overflow-y-auto',
            className
          )}>
            <div className="flex items-center justify-between">
              <div className="flex items-center gap-2">
                <Shield className="h-5 w-5 text-blue-500" />
                <Dialog.Title className="text-lg font-semibold">
                  {t('device_management')}
                </Dialog.Title>
              </div>
              <button
                onClick={handleRefresh}
                disabled={isRefreshing}
                className={cn(
                  'p-2 rounded-md hover:bg-gray-100 dark:hover:bg-gray-700 transition-colors',
                  'focus:outline-none focus:ring-2 focus:ring-blue-500',
                  'disabled:opacity-50 disabled:cursor-not-allowed'
                )}
                aria-label={t('refresh_devices')}
              >
                <RefreshCw className={cn('h-4 w-4', isRefreshing && 'animate-spin')} />
              </button>
            </div>

            <Dialog.Description className="text-sm text-gray-600 dark:text-gray-400">
              {t('device_management_description')}
            </Dialog.Description>

            {/* 統計情報 */}
            <div className="grid grid-cols-3 gap-4">
              <div className="rounded-lg border border-gray-200 dark:border-gray-700 p-3 text-center">
                <div className="text-2xl font-bold text-blue-600 dark:text-blue-400">
                  {deviceStats.total}
                </div>
                <div className="text-sm text-gray-600 dark:text-gray-400">
                  {t('total_devices')}
                </div>
              </div>
              <div className="rounded-lg border border-green-200 dark:border-green-700 p-3 text-center bg-green-50 dark:bg-green-900/20">
                <div className="text-2xl font-bold text-green-600 dark:text-green-400">
                  {deviceStats.verified}
                </div>
                <div className="text-sm text-green-700 dark:text-green-300">
                  {t('verified_devices')}
                </div>
              </div>
              <div className="rounded-lg border border-yellow-200 dark:border-yellow-700 p-3 text-center bg-yellow-50 dark:bg-yellow-900/20">
                <div className="text-2xl font-bold text-yellow-600 dark:text-yellow-400">
                  {deviceStats.unverified}
                </div>
                <div className="text-sm text-yellow-700 dark:text-yellow-300">
                  {t('unverified_devices')}
                </div>
              </div>
            </div>

            {/* フィルター */}
            <div className="flex gap-2">
              {(['all', 'verified', 'unverified'] as const).map((filterOption) => (
                <button
                  key={filterOption}
                  onClick={() => setFilter(filterOption)}
                  className={cn(
                    'px-3 py-1 rounded-md text-sm transition-colors',
                    filter === filterOption
                      ? 'bg-blue-600 text-white'
                      : 'bg-gray-200 dark:bg-gray-700 text-gray-700 dark:text-gray-300 hover:bg-gray-300 dark:hover:bg-gray-600'
                  )}
                >
                  {t(`filter_${filterOption}`)}
                </button>
              ))}
            </div>

            {/* デバイス一覧 */}
            <div className="space-y-3 max-h-96 overflow-y-auto">
              {filteredDevices.map((device) => (
                <div
                  key={device.id}
                  className={cn(
                    'flex items-center justify-between p-4 rounded-lg border transition-colors',
                    device.id === currentDeviceId
                      ? 'border-blue-200 bg-blue-50 dark:border-blue-800 dark:bg-blue-900/20'
                      : 'border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800'
                  )}
                >
                  <div className="flex items-center gap-3">
                    <div className={cn(
                      'p-2 rounded-full',
                      device.verified
                        ? 'bg-green-100 dark:bg-green-900/30 text-green-600 dark:text-green-400'
                        : 'bg-gray-100 dark:bg-gray-700 text-gray-600 dark:text-gray-400'
                    )}>
                      {getDeviceIcon(device.platform)}
                    </div>
                    
                    <div>
                      <div className="flex items-center gap-2">
                        <span className="font-medium">{device.name}</span>
                        {device.id === currentDeviceId && (
                          <span className="px-2 py-1 text-xs bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-300 rounded-md">
                            {t('current_device')}
                          </span>
                        )}
                        {device.verified ? (
                          <ShieldCheck className="h-4 w-4 text-green-500" />
                        ) : (
                          <ShieldAlert className="h-4 w-4 text-yellow-500" />
                        )}
                      </div>
                      <div className="text-sm text-gray-600 dark:text-gray-400">
                        {device.platform} • {formatFingerprint(device.fingerprint)}
                      </div>
                      <div className="text-xs text-gray-500 dark:text-gray-500">
                        {t('last_seen')}: {device.lastSeen.toLocaleString()}
                      </div>
                    </div>
                  </div>

                  {/* アクションボタン */}
                  <div className="flex items-center gap-2">
                    {!device.verified && (
                      <button
                        onClick={() => handleVerifyDevice(device.id)}
                        disabled={verifyingDevices.has(device.id)}
                        className={cn(
                          'px-3 py-1 text-sm rounded-md transition-colors',
                          'bg-green-600 text-white hover:bg-green-700',
                          'disabled:opacity-50 disabled:cursor-not-allowed',
                          'focus:outline-none focus:ring-2 focus:ring-green-500'
                        )}
                      >
                        {verifyingDevices.has(device.id) ? (
                          <RefreshCw className="h-4 w-4 animate-spin" />
                        ) : (
                          <>
                            <Check className="h-4 w-4 mr-1" />
                            {t('verify')}
                          </>
                        )}
                      </button>
                    )}
                    
                    {device.id !== currentDeviceId && (
                      <button
                        onClick={() => setRevokeConfirm(device.id)}
                        disabled={revokingDevices.has(device.id)}
                        className={cn(
                          'px-3 py-1 text-sm rounded-md transition-colors',
                          'bg-red-600 text-white hover:bg-red-700',
                          'disabled:opacity-50 disabled:cursor-not-allowed',
                          'focus:outline-none focus:ring-2 focus:ring-red-500'
                        )}
                      >
                        {revokingDevices.has(device.id) ? (
                          <RefreshCw className="h-4 w-4 animate-spin" />
                        ) : (
                          <>
                            <X className="h-4 w-4 mr-1" />
                            {t('revoke')}
                          </>
                        )}
                      </button>
                    )}
                  </div>
                </div>
              ))}

              {filteredDevices.length === 0 && (
                <div className="text-center py-8 text-gray-500 dark:text-gray-400">
                  {t('no_devices_found')}
                </div>
              )}
            </div>

            {/* セキュリティ警告 */}
            {deviceStats.unverified > 0 && (
              <div className="rounded-lg border border-amber-200 bg-amber-50 p-3 dark:border-amber-800 dark:bg-amber-900/20">
                <div className="flex items-start gap-2">
                  <AlertTriangle className="mt-0.5 h-4 w-4 text-amber-500" />
                  <div className="text-sm text-amber-700 dark:text-amber-300">
                    {t('unverified_devices_warning', { count: deviceStats.unverified })}
                  </div>
                </div>
              </div>
            )}

            {/* 閉じるボタン */}
            <div className="flex justify-end">
              <Dialog.Close asChild>
                <button className="inline-flex h-10 items-center justify-center rounded-md border border-gray-300 bg-transparent px-4 py-2 text-sm font-medium text-gray-700 ring-offset-background transition-colors hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-gray-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 dark:border-gray-700 dark:text-gray-300 dark:hover:bg-gray-700">
                  {t('close')}
                </button>
              </Dialog.Close>
            </div>
          </Dialog.Content>
        </Dialog.Portal>
      </Dialog.Root>

      {/* デバイス取り消し確認ダイアログ */}
      <AlertDialog.Root open={!!revokeConfirm} onOpenChange={() => setRevokeConfirm(null)}>
        <AlertDialog.Portal>
          <AlertDialog.Overlay className="fixed inset-0 z-50 bg-black/50 backdrop-blur-sm" />
          <AlertDialog.Content className="fixed left-[50%] top-[50%] z-50 grid w-full max-w-md translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 rounded-lg border-gray-200 bg-white dark:border-gray-700 dark:bg-gray-800">
            <div className="flex flex-col space-y-2 text-center sm:text-left">
              <AlertDialog.Title className="flex items-center gap-2 text-lg font-semibold">
                <AlertTriangle className="h-5 w-5 text-red-500" />
                {t('confirm_revoke_device')}
              </AlertDialog.Title>
              <AlertDialog.Description className="text-sm text-gray-600 dark:text-gray-400">
                {t('revoke_device_warning', {
                  deviceName: devices.find(d => d.id === revokeConfirm)?.name || t('unknown_device')
                })}
              </AlertDialog.Description>
            </div>
            <div className="flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2 space-y-2 space-y-reverse sm:space-y-0">
              <AlertDialog.Cancel asChild>
                <button className="inline-flex h-10 items-center justify-center rounded-md border border-gray-300 bg-transparent px-4 py-2 text-sm font-medium text-gray-700 ring-offset-background transition-colors hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-gray-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 dark:border-gray-700 dark:text-gray-300 dark:hover:bg-gray-700">
                  {t('cancel')}
                </button>
              </AlertDialog.Cancel>
              <AlertDialog.Action asChild>
                <button
                  onClick={() => revokeConfirm && handleRevokeDevice(revokeConfirm)}
                  className="inline-flex h-10 items-center justify-center rounded-md bg-red-600 px-4 py-2 text-sm font-medium text-white ring-offset-background transition-colors hover:bg-red-700 focus:outline-none focus:ring-2 focus:ring-red-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"
                >
                  {t('revoke_device')}
                </button>
              </AlertDialog.Action>
            </div>
          </AlertDialog.Content>
        </AlertDialog.Portal>
      </AlertDialog.Root>
    </>
  );
}