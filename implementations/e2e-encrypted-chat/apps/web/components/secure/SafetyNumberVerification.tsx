'use client';

import React, { useState, useCallback, useRef } from 'react';
import { Check, X, Copy, RefreshCw, Eye, EyeOff, Shield, AlertTriangle, QrCode } from 'lucide-react';
import * as Dialog from '@radix-ui/react-dialog';
import * as AlertDialog from '@radix-ui/react-alert-dialog';
import { useTranslations } from 'next-intl';
import { cn } from '@/lib/utils';
import { useTelemetry } from '@/hooks/use-telemetry';
import type { SafetyNumber } from '@/types/security';

interface SafetyNumberVerificationProps {
  safetyNumber: SafetyNumber;
  contactName: string;
  onVerify: () => Promise<void>;
  onRegenerate?: () => Promise<void>;
  isOpen: boolean;
  onClose: () => void;
  className?: string;
}

export function SafetyNumberVerification({
  safetyNumber,
  contactName,
  onVerify,
  onRegenerate,
  isOpen,
  onClose,
  className,
}: SafetyNumberVerificationProps) {
  const t = useTranslations('verification');
  const { trackUIInteraction, trackVerification, createSecuritySpan } = useTelemetry();
  
  const [isVerifying, setIsVerifying] = useState(false);
  const [isRegenerating, setIsRegenerating] = useState(false);
  const [showFullNumbers, setShowFullNumbers] = useState(false);
  const [showRegenConfirm, setShowRegenConfirm] = useState(false);
  const [copiedField, setCopiedField] = useState<'local' | 'remote' | null>(null);
  const copyTimeoutRef = useRef<NodeJS.Timeout | null>(null);

  // 安全番号の表示形式（5桁ずつのグループ）
  const formatSafetyNumber = useCallback((number: string, maskPartial: boolean = false) => {
    const cleanNumber = number.replace(/\D/g, '');
    if (maskPartial && !showFullNumbers) {
      const visible = cleanNumber.slice(0, 10) + '*'.repeat(cleanNumber.length - 20) + cleanNumber.slice(-10);
      return visible.replace(/(\d{5})/g, '$1 ').trim();
    }
    return cleanNumber.replace(/(\d{5})/g, '$1 ').trim();
  }, [showFullNumbers]);

  // コピー機能
  const handleCopy = async (text: string, field: 'local' | 'remote') => {
    try {
      await navigator.clipboard.writeText(text);
      setCopiedField(field);
      trackUIInteraction('SafetyNumberVerification', `copy_${field}_number`);
      
      if (copyTimeoutRef.current) {
        clearTimeout(copyTimeoutRef.current);
      }
      
      copyTimeoutRef.current = setTimeout(() => {
        setCopiedField(null);
      }, 2000);
    } catch (error) {
      console.error('Failed to copy to clipboard:', error);
    }
  };

  // 検証処理
  const handleVerify = async () => {
    setIsVerifying(true);
    const span = createSecuritySpan('safety_number_verification');
    
    try {
      await onVerify();
      trackVerification('safety_number', true);
      trackUIInteraction('SafetyNumberVerification', 'verify_success');
      span.setAttributes({ 'verification.success': true });
      onClose();
    } catch (error) {
      trackVerification('safety_number', false);
      trackUIInteraction('SafetyNumberVerification', 'verify_failed');
      span.recordException(error as Error);
      span.setAttributes({ 'verification.success': false });
    } finally {
      span.end();
      setIsVerifying(false);
    }
  };

  // 再生成処理
  const handleRegenerate = async () => {
    if (!onRegenerate) return;
    
    setIsRegenerating(true);
    const span = createSecuritySpan('safety_number_regeneration');
    
    try {
      await onRegenerate();
      trackUIInteraction('SafetyNumberVerification', 'regenerate_success');
      span.setAttributes({ 'regeneration.success': true });
      setShowRegenConfirm(false);
    } catch (error) {
      trackUIInteraction('SafetyNumberVerification', 'regenerate_failed');
      span.recordException(error as Error);
      span.setAttributes({ 'regeneration.success': false });
    } finally {
      span.end();
      setIsRegenerating(false);
    }
  };

  // QRコード表示（実装は省略、実際のプロダクションでは生成）
  const generateQRCodeData = () => {
    return `safety-number:${safetyNumber.localNumber}:${safetyNumber.remoteNumber}`;
  };

  return (
    <>
      <Dialog.Root open={isOpen} onOpenChange={onClose}>
        <Dialog.Portal>
          <Dialog.Overlay className="fixed inset-0 z-50 bg-black/50 backdrop-blur-sm data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0" />
          <Dialog.Content className={cn(
            'fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200',
            'data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0 data-[state=closed]:zoom-out-95 data-[state=open]:zoom-in-95 data-[state=closed]:slide-out-to-left-1/2 data-[state=closed]:slide-out-to-top-[48%] data-[state=open]:slide-in-from-left-1/2 data-[state=open]:slide-in-from-top-[48%]',
            'rounded-lg border-gray-200 bg-white dark:border-gray-700 dark:bg-gray-800',
            className
          )}>
            <div className="flex flex-col space-y-2 text-center sm:text-left">
              <Dialog.Title className="flex items-center gap-2 text-lg font-semibold">
                <Shield className="h-5 w-5 text-blue-500" />
                {t('verify_safety_number')}
              </Dialog.Title>
              <Dialog.Description className="text-sm text-gray-600 dark:text-gray-400">
                {t('safety_number_description', { contact: contactName })}
              </Dialog.Description>
            </div>

            <div className="space-y-6">
              {/* 検証ステータス */}
              <div className={cn(
                'flex items-center gap-3 rounded-lg border p-3',
                safetyNumber.verified
                  ? 'border-green-200 bg-green-50 dark:border-green-800 dark:bg-green-900/20'
                  : 'border-yellow-200 bg-yellow-50 dark:border-yellow-800 dark:bg-yellow-900/20'
              )}>
                {safetyNumber.verified ? (
                  <>
                    <Check className="h-5 w-5 text-green-500" />
                    <div>
                      <div className="font-medium text-green-700 dark:text-green-300">
                        {t('verified')}
                      </div>
                      {safetyNumber.lastVerified && (
                        <div className="text-sm text-green-600 dark:text-green-400">
                          {t('last_verified')}: {safetyNumber.lastVerified.toLocaleDateString()}
                        </div>
                      )}
                    </div>
                  </>
                ) : (
                  <>
                    <AlertTriangle className="h-5 w-5 text-yellow-500" />
                    <div>
                      <div className="font-medium text-yellow-700 dark:text-yellow-300">
                        {t('not_verified')}
                      </div>
                      <div className="text-sm text-yellow-600 dark:text-yellow-400">
                        {t('verification_required')}
                      </div>
                    </div>
                  </>
                )}
              </div>

              {/* 可視性トグル */}
              <div className="flex items-center justify-between">
                <span className="text-sm font-medium">{t('show_full_numbers')}</span>
                <button
                  onClick={() => {
                    setShowFullNumbers(!showFullNumbers);
                    trackUIInteraction('SafetyNumberVerification', `toggle_visibility_${!showFullNumbers}`);
                  }}
                  className="flex items-center gap-2 text-sm text-blue-600 hover:text-blue-700 dark:text-blue-400 dark:hover:text-blue-300"
                >
                  {showFullNumbers ? <EyeOff className="h-4 w-4" /> : <Eye className="h-4 w-4" />}
                  {showFullNumbers ? t('hide') : t('show')}
                </button>
              </div>

              {/* ローカル安全番号 */}
              <div className="space-y-2">
                <label className="text-sm font-medium">{t('your_safety_number')}</label>
                <div className="relative">
                  <div className={cn(
                    'font-mono text-sm p-3 bg-gray-50 dark:bg-gray-900 border border-gray-200 dark:border-gray-700 rounded-md',
                    'select-all break-all'
                  )}>
                    {formatSafetyNumber(safetyNumber.localNumber, true)}
                  </div>
                  <button
                    onClick={() => handleCopy(safetyNumber.localNumber, 'local')}
                    className={cn(
                      'absolute right-2 top-2 p-1 rounded hover:bg-gray-200 dark:hover:bg-gray-700',
                      'transition-colors duration-200'
                    )}
                    aria-label={t('copy_local_number')}
                  >
                    {copiedField === 'local' ? (
                      <Check className="h-4 w-4 text-green-500" />
                    ) : (
                      <Copy className="h-4 w-4 text-gray-500" />
                    )}
                  </button>
                </div>
              </div>

              {/* リモート安全番号 */}
              <div className="space-y-2">
                <label className="text-sm font-medium">{t('contact_safety_number', { contact: contactName })}</label>
                <div className="relative">
                  <div className={cn(
                    'font-mono text-sm p-3 bg-gray-50 dark:bg-gray-900 border border-gray-200 dark:border-gray-700 rounded-md',
                    'select-all break-all'
                  )}>
                    {formatSafetyNumber(safetyNumber.remoteNumber, true)}
                  </div>
                  <button
                    onClick={() => handleCopy(safetyNumber.remoteNumber, 'remote')}
                    className={cn(
                      'absolute right-2 top-2 p-1 rounded hover:bg-gray-200 dark:hover:bg-gray-700',
                      'transition-colors duration-200'
                    )}
                    aria-label={t('copy_contact_number')}
                  >
                    {copiedField === 'remote' ? (
                      <Check className="h-4 w-4 text-green-500" />
                    ) : (
                      <Copy className="h-4 w-4 text-gray-500" />
                    )}
                  </button>
                </div>
              </div>

              {/* QRコードオプション */}
              <div className="flex justify-center">
                <button
                  className={cn(
                    'flex items-center gap-2 px-4 py-2 text-sm rounded-md',
                    'border border-gray-300 dark:border-gray-600 hover:bg-gray-50 dark:hover:bg-gray-700',
                    'transition-colors duration-200'
                  )}
                  onClick={() => trackUIInteraction('SafetyNumberVerification', 'show_qr_code')}
                >
                  <QrCode className="h-4 w-4" />
                  {t('show_qr_code')}
                </button>
              </div>

              {/* 警告メッセージ */}
              <div className="rounded-lg border border-amber-200 bg-amber-50 p-3 dark:border-amber-800 dark:bg-amber-900/20">
                <div className="flex items-start gap-2">
                  <AlertTriangle className="mt-0.5 h-4 w-4 text-amber-500" />
                  <div className="text-sm text-amber-700 dark:text-amber-300">
                    {t('verification_warning')}
                  </div>
                </div>
              </div>
            </div>

            {/* アクションボタン */}
            <div className="flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2 space-y-2 space-y-reverse sm:space-y-0">
              <Dialog.Close asChild>
                <button className="inline-flex h-10 items-center justify-center rounded-md border border-gray-300 bg-transparent px-4 py-2 text-sm font-medium text-gray-700 ring-offset-background transition-colors hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-gray-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 dark:border-gray-700 dark:text-gray-300 dark:hover:bg-gray-700 dark:focus:ring-gray-300">
                  {t('cancel')}
                </button>
              </Dialog.Close>
              
              {onRegenerate && (
                <button
                  onClick={() => setShowRegenConfirm(true)}
                  disabled={isRegenerating}
                  className="inline-flex h-10 items-center justify-center rounded-md border border-gray-300 bg-transparent px-4 py-2 text-sm font-medium text-gray-700 ring-offset-background transition-colors hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-gray-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 dark:border-gray-700 dark:text-gray-300 dark:hover:bg-gray-700 dark:focus:ring-gray-300"
                >
                  {isRegenerating ? (
                    <RefreshCw className="mr-2 h-4 w-4 animate-spin" />
                  ) : (
                    <RefreshCw className="mr-2 h-4 w-4" />
                  )}
                  {t('regenerate')}
                </button>
              )}
              
              <button
                onClick={handleVerify}
                disabled={isVerifying}
                className={cn(
                  'inline-flex h-10 items-center justify-center rounded-md px-4 py-2 text-sm font-medium text-white',
                  'ring-offset-background transition-colors focus:outline-none focus:ring-2 focus:ring-offset-2',
                  'disabled:cursor-not-allowed disabled:opacity-50',
                  safetyNumber.verified
                    ? 'bg-green-600 hover:bg-green-700 focus:ring-green-950'
                    : 'bg-blue-600 hover:bg-blue-700 focus:ring-blue-950'
                )}
              >
                {isVerifying ? (
                  <RefreshCw className="mr-2 h-4 w-4 animate-spin" />
                ) : safetyNumber.verified ? (
                  <Check className="mr-2 h-4 w-4" />
                ) : (
                  <Shield className="mr-2 h-4 w-4" />
                )}
                {safetyNumber.verified ? t('verified') : t('verify')}
              </button>
            </div>
          </Dialog.Content>
        </Dialog.Portal>
      </Dialog.Root>

      {/* 再生成確認ダイアログ */}
      <AlertDialog.Root open={showRegenConfirm} onOpenChange={setShowRegenConfirm}>
        <AlertDialog.Portal>
          <AlertDialog.Overlay className="fixed inset-0 z-50 bg-black/50 backdrop-blur-sm" />
          <AlertDialog.Content className="fixed left-[50%] top-[50%] z-50 grid w-full max-w-md translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 rounded-lg border-gray-200 bg-white dark:border-gray-700 dark:bg-gray-800">
            <div className="flex flex-col space-y-2 text-center sm:text-left">
              <AlertDialog.Title className="text-lg font-semibold">
                {t('confirm_regenerate')}
              </AlertDialog.Title>
              <AlertDialog.Description className="text-sm text-gray-600 dark:text-gray-400">
                {t('regenerate_warning')}
              </AlertDialog.Description>
            </div>
            <div className="flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2">
              <AlertDialog.Cancel asChild>
                <button className="inline-flex h-10 items-center justify-center rounded-md border border-gray-300 bg-transparent px-4 py-2 text-sm font-medium text-gray-700 ring-offset-background transition-colors hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-gray-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 dark:border-gray-700 dark:text-gray-300 dark:hover:bg-gray-700">
                  {t('cancel')}
                </button>
              </AlertDialog.Cancel>
              <AlertDialog.Action asChild>
                <button
                  onClick={handleRegenerate}
                  className="inline-flex h-10 items-center justify-center rounded-md bg-red-600 px-4 py-2 text-sm font-medium text-white ring-offset-background transition-colors hover:bg-red-700 focus:outline-none focus:ring-2 focus:ring-red-950 focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"
                >
                  {t('regenerate')}
                </button>
              </AlertDialog.Action>
            </div>
          </AlertDialog.Content>
        </AlertDialog.Portal>
      </AlertDialog.Root>
    </>
  );
}