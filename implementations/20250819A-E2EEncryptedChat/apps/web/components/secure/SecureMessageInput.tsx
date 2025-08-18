'use client';

import React, { useState, useCallback, useRef, useEffect } from 'react';
import { useForm } from 'react-hook-form';
import { zodResolver } from '@hookform/resolvers/zod';
import { z } from 'zod';
import { Send, Shield, AlertTriangle } from 'lucide-react';
import { useTranslations } from 'next-intl';
import { cn, sanitizeInput } from '@/lib/utils';
import { useTelemetry } from '@/hooks/use-telemetry';

const messageSchema = z.object({
  content: z
    .string()
    .min(1, 'Message cannot be empty')
    .max(4000, 'Message too long')
    .refine((val) => val.trim().length > 0, 'Message cannot be only whitespace'),
});

type MessageFormData = z.infer<typeof messageSchema>;

interface SecureMessageInputProps {
  onSendMessage: (content: string) => Promise<void>;
  encryptionEnabled: boolean;
  isConnected: boolean;
  recipientVerified: boolean;
  className?: string;
  disabled?: boolean;
  maxLength?: number;
}

export function SecureMessageInput({
  onSendMessage,
  encryptionEnabled,
  isConnected,
  recipientVerified,
  className,
  disabled = false,
  maxLength = 4000,
}: SecureMessageInputProps) {
  const t = useTranslations('chat');
  const { trackUIInteraction, trackMessageSent, startEncryptionSpan, endEncryptionSpan } = useTelemetry();
  
  const [isSending, setIsSending] = useState(false);
  const [lastSentTime, setLastSentTime] = useState<Date | null>(null);
  const textareaRef = useRef<HTMLTextAreaElement>(null);
  const rateLimitRef = useRef<{ count: number; lastReset: Date }>({
    count: 0,
    lastReset: new Date(),
  });

  const {
    register,
    handleSubmit,
    formState: { errors, isValid },
    reset,
    watch,
    setValue,
  } = useForm<MessageFormData>({
    resolver: zodResolver(messageSchema),
    mode: 'onChange',
    defaultValues: {
      content: '',
    },
  });

  const messageContent = watch('content');
  const currentLength = messageContent?.length || 0;

  // レート制限チェック
  const checkRateLimit = useCallback(() => {
    const now = new Date();
    const timeSinceReset = now.getTime() - rateLimitRef.current.lastReset.getTime();
    
    // 1分間のウィンドウをリセット
    if (timeSinceReset > 60000) {
      rateLimitRef.current = { count: 0, lastReset: now };
    }
    
    // 1分間に30メッセージの制限
    if (rateLimitRef.current.count >= 30) {
      return false;
    }
    
    return true;
  }, []);

  // テキストエリアの自動リサイズ
  const adjustTextareaHeight = useCallback(() => {
    const textarea = textareaRef.current;
    if (textarea) {
      textarea.style.height = 'auto';
      textarea.style.height = `${Math.min(textarea.scrollHeight, 150)}px`;
    }
  }, []);

  useEffect(() => {
    adjustTextareaHeight();
  }, [messageContent, adjustTextareaHeight]);

  // セキュアな送信処理
  const onSubmit = handleSubmit(async (data: MessageFormData) => {
    if (!checkRateLimit()) {
      trackUIInteraction('SecureMessageInput', 'rate_limit_exceeded');
      return;
    }

    if (!isConnected) {
      trackUIInteraction('SecureMessageInput', 'send_while_disconnected');
      return;
    }

    setIsSending(true);
    const startTime = Date.now();
    let encryptionSpanId: string | null = null;

    try {
      // 入力のサニタイズ
      const sanitizedContent = sanitizeInput(data.content);
      
      if (encryptionEnabled) {
        encryptionSpanId = startEncryptionSpan('encrypt');
      }

      // メッセージ送信
      await onSendMessage(sanitizedContent);
      
      if (encryptionSpanId) {
        endEncryptionSpan(encryptionSpanId, Date.now() - startTime, true);
      }
      
      // メトリクス記録
      trackMessageSent(encryptionEnabled, encryptionEnabled ? 'AES-256' : 'none');
      trackUIInteraction('SecureMessageInput', 'message_sent');
      
      // フォームリセット
      reset();
      setLastSentTime(new Date());
      rateLimitRef.current.count += 1;
      
    } catch (error) {
      if (encryptionSpanId) {
        endEncryptionSpan(encryptionSpanId, Date.now() - startTime, false);
      }
      trackUIInteraction('SecureMessageInput', 'send_failed');
      console.error('Failed to send message:', error);
    } finally {
      setIsSending(false);
    }
  });

  // キーボードショートカット
  const handleKeyDown = useCallback(
    (e: React.KeyboardEvent<HTMLTextAreaElement>) => {
      if (e.key === 'Enter' && !e.shiftKey && !disabled && isValid && !isSending) {
        e.preventDefault();
        onSubmit();
      }
    },
    [disabled, isValid, isSending, onSubmit]
  );

  // セキュリティ状態の表示
  const getSecurityIcon = () => {
    if (!isConnected) {
      return <AlertTriangle className="h-4 w-4 text-red-500" />;
    }
    if (encryptionEnabled && recipientVerified) {
      return <Shield className="h-4 w-4 text-green-500" />;
    }
    return <Shield className="h-4 w-4 text-yellow-500" />;
  };

  const getSecurityMessage = () => {
    if (!isConnected) {
      return t('disconnected');
    }
    if (encryptionEnabled && recipientVerified) {
      return t('encrypted_and_verified');
    }
    if (encryptionEnabled) {
      return t('encrypted_not_verified');
    }
    return t('not_encrypted');
  };

  return (
    <div className={cn('border-t border-gray-200 dark:border-gray-700 p-4', className)}>
      {/* セキュリティ状態表示 */}
      <div className="flex items-center gap-2 mb-3 text-sm">
        {getSecurityIcon()}
        <span className={cn(
          'font-medium',
          !isConnected && 'text-red-600 dark:text-red-400',
          encryptionEnabled && recipientVerified && 'text-green-600 dark:text-green-400',
          encryptionEnabled && !recipientVerified && 'text-yellow-600 dark:text-yellow-400',
          !encryptionEnabled && 'text-gray-600 dark:text-gray-400'
        )}>
          {getSecurityMessage()}
        </span>
      </div>

      {/* メッセージ入力フォーム */}
      <form onSubmit={onSubmit} className="relative">
        <div className="relative">
          <textarea
            ref={textareaRef}
            {...register('content')}
            placeholder={t('type_message')}
            disabled={disabled || isSending || !isConnected}
            onKeyDown={handleKeyDown}
            className={cn(
              'w-full resize-none rounded-lg border border-gray-300 dark:border-gray-600',
              'bg-white dark:bg-gray-800 text-gray-900 dark:text-gray-100',
              'px-4 py-3 pr-12 focus:ring-2 focus:ring-blue-500 focus:border-transparent',
              'disabled:opacity-50 disabled:cursor-not-allowed',
              'placeholder:text-gray-500 dark:placeholder:text-gray-400',
              errors.content && 'border-red-500 focus:ring-red-500',
              'min-h-[44px] max-h-[150px]'
            )}
            rows={1}
            maxLength={maxLength}
            aria-label={t('message_input_label')}
            aria-describedby="message-length message-error"
          />
          
          {/* 送信ボタン */}
          <button
            type="submit"
            disabled={disabled || isSending || !isValid || !isConnected || currentLength === 0}
            className={cn(
              'absolute right-2 bottom-2 rounded-full p-2',
              'bg-blue-600 text-white hover:bg-blue-700',
              'disabled:opacity-50 disabled:cursor-not-allowed disabled:hover:bg-blue-600',
              'focus:outline-none focus:ring-2 focus:ring-blue-500 focus:ring-offset-2',
              'transition-colors duration-200'
            )}
            aria-label={t('send_message')}
          >
            <Send className="h-4 w-4" />
          </button>
        </div>

        {/* 文字数カウンターとエラー表示 */}
        <div className="flex justify-between items-center mt-2 text-sm">
          <div>
            {errors.content && (
              <span id="message-error" className="text-red-600 dark:text-red-400">
                {errors.content.message}
              </span>
            )}
          </div>
          <div
            id="message-length"
            className={cn(
              'text-gray-500 dark:text-gray-400',
              currentLength > maxLength * 0.8 && 'text-yellow-600 dark:text-yellow-400',
              currentLength >= maxLength && 'text-red-600 dark:text-red-400'
            )}
          >
            {currentLength}/{maxLength}
          </div>
        </div>

        {/* レート制限警告 */}
        {rateLimitRef.current.count > 25 && (
          <div className="mt-2 text-sm text-yellow-600 dark:text-yellow-400">
            {t('rate_limit_warning')}
          </div>
        )}
      </form>
    </div>
  );
}