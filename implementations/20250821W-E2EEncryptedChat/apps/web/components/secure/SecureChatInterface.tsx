'use client';

import { useState, useEffect, useRef, useCallback } from 'react';
import { useTranslations } from 'next-intl';
import { Shield, ShieldCheck, ShieldX, Lock, Unlock, AlertTriangle, Send, Phone, Video, MoreVertical } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Card, CardHeader, CardContent } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from '@/components/ui/tooltip';
import { Alert, AlertDescription } from '@/components/ui/alert';
import { DropdownMenu, DropdownMenuContent, DropdownMenuItem, DropdownMenuTrigger } from '@/components/ui/dropdown-menu';
import { useSecurityTelemetry } from '@/lib/hooks/useSecurityTelemetry';
import { EncryptionStatusIndicator } from './EncryptionStatusIndicator';
import { SafetyNumberVerification } from './SafetyNumberVerification';
import { SecureMessageInput } from './SecureMessageInput';
import type { SecureSession, EncryptedMessage, User, SecurityLevel } from '@/types/crypto';

interface SecureChatInterfaceProps {
  session: SecureSession;
  currentUser: User;
  messages: EncryptedMessage[];
  onSendMessage: (message: string) => Promise<void>;
  onVerifyIdentity: () => void;
  onStartVoiceCall: () => void;
  onStartVideoCall: () => void;
  className?: string;
}

export function SecureChatInterface({
  session,
  currentUser,
  messages,
  onSendMessage,
  onVerifyIdentity,
  onStartVoiceCall,
  onStartVideoCall,
  className = ''
}: SecureChatInterfaceProps) {
  const t = useTranslations('chat');
  const tSecurity = useTranslations('security');
  
  const [isVerificationOpen, setIsVerificationOpen] = useState(false);
  const [securityLevel, setSecurityLevel] = useState<SecurityLevel>('HIGH');
  const [isTyping, setIsTyping] = useState(false);
  const [lastSeen, setLastSeen] = useState<Date | null>(null);
  
  const messagesEndRef = useRef<HTMLDivElement>(null);
  const chatContainerRef = useRef<HTMLDivElement>(null);
  
  const { recordSecurityEvent, recordUIInteraction } = useSecurityTelemetry();

  // セキュリティレベル監視
  useEffect(() => {
    const checkSecurityLevel = () => {
      if (!session.isVerified) {
        setSecurityLevel('WARNING');
      } else if (session.keyRotationCount < 1) {
        setSecurityLevel('MEDIUM');  
      } else {
        setSecurityLevel('HIGH');
      }
    };

    checkSecurityLevel();
    const interval = setInterval(checkSecurityLevel, 30000); // 30秒間隔
    
    return () => clearInterval(interval);
  }, [session]);

  // メッセージ自動スクロール
  useEffect(() => {
    if (messagesEndRef.current) {
      messagesEndRef.current.scrollIntoView({ behavior: 'smooth' });
    }
  }, [messages]);

  // セキュリティイベント記録
  const handleSecurityAction = useCallback((action: string, details?: any) => {
    recordSecurityEvent({
      type: action,
      sessionId: session.id,
      userId: currentUser.id,
      timestamp: new Date(),
      details
    });
  }, [recordSecurityEvent, session.id, currentUser.id]);

  // UI インタラクション記録
  const handleUIInteraction = useCallback((element: string, action: string) => {
    recordUIInteraction({
      element,
      action,
      sessionId: session.id,
      timestamp: new Date()
    });
  }, [recordUIInteraction, session.id]);

  // メッセージ送信処理
  const handleSendMessage = async (message: string) => {
    try {
      handleUIInteraction('message-send', 'click');
      handleSecurityAction('MESSAGE_SENT', { messageLength: message.length });
      
      await onSendMessage(message);
      
      // 送信成功のテレメトリ
      recordSecurityEvent({
        type: 'MESSAGE_ENCRYPTED',
        sessionId: session.id,
        userId: currentUser.id,
        timestamp: new Date(),
        details: { success: true, encryptionAlgorithm: 'AES-256-GCM' }
      });

    } catch (error) {
      // 送信失敗のテレメトリ
      recordSecurityEvent({
        type: 'MESSAGE_ENCRYPTION_FAILED',
        sessionId: session.id,
        userId: currentUser.id,
        timestamp: new Date(),
        details: { error: error.message }
      });
      
      throw error;
    }
  };

  // セキュリティアイコン取得
  const getSecurityIcon = () => {
    switch (securityLevel) {
      case 'HIGH':
        return <ShieldCheck className="w-4 h-4 text-green-500" aria-label={t('security.high')} />;
      case 'MEDIUM':
        return <Shield className="w-4 h-4 text-yellow-500" aria-label={t('security.medium')} />;
      case 'WARNING':
        return <AlertTriangle className="w-4 h-4 text-orange-500" aria-label={t('security.warning')} />;
      default:
        return <ShieldX className="w-4 h-4 text-red-500" aria-label={t('security.error')} />;
    }
  };

  // セキュリティステータステキスト
  const getSecurityStatusText = () => {
    const otherUser = session.participants.find(p => p !== currentUser.id);
    const baseText = t('security.encrypted_with', { user: otherUser });

    if (!session.isVerified) {
      return t('security.unverified_warning');
    }
    
    return baseText;
  };

  return (
    <TooltipProvider>
      <div className={`flex flex-col h-full bg-background ${className}`} role="main" aria-label={t('main.chat_interface')}>
        
        {/* セキュリティステータスヘッダー */}
        <Card className="rounded-none border-x-0 border-t-0">
          <CardHeader className="p-4 bg-muted/50">
            <div className="flex items-center justify-between">
              <div className="flex items-center gap-3">
                {getSecurityIcon()}
                <div>
                  <p className="text-sm font-medium" id="security-status">
                    {getSecurityStatusText()}
                  </p>
                  {securityLevel === 'WARNING' && (
                    <p className="text-xs text-muted-foreground">
                      {t('security.verify_to_secure')}
                    </p>
                  )}
                </div>
                
                <EncryptionStatusIndicator 
                  session={session}
                  className="ml-2"
                />
              </div>

              <div className="flex items-center gap-2">
                {/* 通話アクション */}
                <Tooltip>
                  <TooltipTrigger asChild>
                    <Button
                      variant="ghost"
                      size="sm"
                      onClick={() => {
                        handleUIInteraction('voice-call', 'click');
                        onStartVoiceCall();
                      }}
                      aria-label={t('actions.voice_call')}
                    >
                      <Phone className="w-4 h-4" />
                    </Button>
                  </TooltipTrigger>
                  <TooltipContent>
                    {t('actions.voice_call')}
                  </TooltipContent>
                </Tooltip>

                <Tooltip>
                  <TooltipTrigger asChild>
                    <Button
                      variant="ghost"
                      size="sm"
                      onClick={() => {
                        handleUIInteraction('video-call', 'click');
                        onStartVideoCall();
                      }}
                      aria-label={t('actions.video_call')}
                    >
                      <Video className="w-4 h-4" />
                    </Button>
                  </TooltipTrigger>
                  <TooltipContent>
                    {t('actions.video_call')}
                  </TooltipContent>
                </Tooltip>

                {/* メニュー */}
                <DropdownMenu>
                  <DropdownMenuTrigger asChild>
                    <Button variant="ghost" size="sm" aria-label={t('actions.menu')}>
                      <MoreVertical className="w-4 h-4" />
                    </Button>
                  </DropdownMenuTrigger>
                  <DropdownMenuContent align="end">
                    <DropdownMenuItem
                      onClick={() => {
                        handleUIInteraction('verify-identity', 'click');
                        setIsVerificationOpen(true);
                      }}
                    >
                      <Shield className="w-4 h-4 mr-2" />
                      {t('actions.verify_identity')}
                    </DropdownMenuItem>
                    <DropdownMenuItem
                      onClick={() => {
                        handleSecurityAction('KEY_ROTATION_REQUESTED');
                        // キーローテーション処理
                      }}
                    >
                      <Lock className="w-4 h-4 mr-2" />
                      {t('actions.rotate_keys')}
                    </DropdownMenuItem>
                  </DropdownMenuContent>
                </DropdownMenu>
              </div>
            </div>

            {/* セキュリティ警告 */}
            {securityLevel === 'WARNING' && (
              <Alert className="mt-3">
                <AlertTriangle className="w-4 h-4" />
                <AlertDescription>
                  {t('security.identity_verification_required')}
                  <Button
                    variant="link" 
                    className="p-0 h-auto font-medium ml-2"
                    onClick={() => setIsVerificationOpen(true)}
                  >
                    {t('actions.verify_now')}
                  </Button>
                </AlertDescription>
              </Alert>
            )}
          </CardHeader>
        </Card>

        {/* メッセージ履歴 */}
        <div 
          ref={chatContainerRef}
          className="flex-1 overflow-y-auto p-4 space-y-4"
          role="log"
          aria-label={t('messages.history')}
          aria-live="polite"
        >
          {messages.map((message, index) => (
            <div
              key={message.id}
              className={`flex ${message.senderId === currentUser.id ? 'justify-end' : 'justify-start'}`}
            >
              <Card className={`max-w-xs md:max-w-md ${
                message.senderId === currentUser.id
                  ? 'bg-primary text-primary-foreground'
                  : 'bg-muted'
              }`}>
                <CardContent className="p-3">
                  <p className="text-sm">{message.content}</p>
                  <div className="flex items-center justify-between mt-2 text-xs opacity-70">
                    <span>{new Date(message.timestamp).toLocaleTimeString()}</span>
                    <div className="flex items-center gap-1">
                      <Lock className="w-3 h-3" aria-label={t('security.encrypted')} />
                      {message.senderId === currentUser.id && (
                        <Badge variant="secondary" className="text-xs">
                          {message.status === 'delivered' ? '✓✓' : '✓'}
                        </Badge>
                      )}
                    </div>
                  </div>
                </CardContent>
              </Card>
            </div>
          ))}
          
          {isTyping && (
            <div className="flex justify-start">
              <Card className="bg-muted">
                <CardContent className="p-3">
                  <div className="flex items-center space-x-1">
                    <div className="flex space-x-1">
                      <div className="w-2 h-2 bg-muted-foreground rounded-full animate-bounce" />
                      <div className="w-2 h-2 bg-muted-foreground rounded-full animate-bounce delay-100" />
                      <div className="w-2 h-2 bg-muted-foreground rounded-full animate-bounce delay-200" />
                    </div>
                    <span className="text-xs text-muted-foreground ml-2">
                      {t('messages.typing')}
                    </span>
                  </div>
                </CardContent>
              </Card>
            </div>
          )}
          
          <div ref={messagesEndRef} />
        </div>

        {/* セキュアメッセージ入力 */}
        <div className="p-4 border-t bg-background">
          <SecureMessageInput
            onSendMessage={handleSendMessage}
            disabled={!session.isActive}
            placeholder={t('input.type_secure_message')}
            maxLength={10000}
            showEncryptionIndicator
            className="w-full"
            ariaLabel={t('input.message_composition')}
          />
          
          {lastSeen && (
            <p className="text-xs text-muted-foreground mt-2">
              {t('status.last_seen', { time: lastSeen.toLocaleTimeString() })}
            </p>
          )}
        </div>

        {/* 身元検証ダイアログ */}
        {isVerificationOpen && (
          <SafetyNumberVerification
            session={session}
            currentUser={currentUser}
            isOpen={isVerificationOpen}
            onClose={() => setIsVerificationOpen(false)}
            onVerificationComplete={(verified) => {
              setIsVerificationOpen(false);
              if (verified) {
                handleSecurityAction('IDENTITY_VERIFIED');
                setSecurityLevel('HIGH');
              }
            }}
          />
        )}
      </div>
    </TooltipProvider>
  );
}

// アクセシビリティ用のキーボードショートカット
export function useSecureChatKeyboardShortcuts(
  onVerifyIdentity: () => void,
  onRotateKeys: () => void,
  onToggleEncryption: () => void
) {
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      // Ctrl/Cmd + E: 身元検証
      if ((event.ctrlKey || event.metaKey) && event.key === 'e') {
        event.preventDefault();
        onVerifyIdentity();
      }
      
      // Ctrl/Cmd + Shift + R: キーローテーション
      if ((event.ctrlKey || event.metaKey) && event.shiftKey && event.key === 'R') {
        event.preventDefault();
        onRotateKeys();
      }
      
      // Ctrl/Cmd + Shift + E: 暗号化切り替え
      if ((event.ctrlKey || event.metaKey) && event.shiftKey && event.key === 'E') {
        event.preventDefault();
        onToggleEncryption();
      }
    };

    document.addEventListener('keydown', handleKeyDown);
    return () => document.removeEventListener('keydown', handleKeyDown);
  }, [onVerifyIdentity, onRotateKeys, onToggleEncryption]);
}