import { Metadata } from 'next';
import { notFound } from 'next/navigation';
import { getTranslations } from 'next-intl/server';
import { SecureChatInterface } from '@/components/secure/SecureChatInterface';
import { validateSessionId } from '@/lib/utils';
import type { ChatSession, SecureMessage, DeviceInfo } from '@/types/security';

// メタデータ生成（セキュリティを考慮して最小限の情報のみ）
export async function generateMetadata({ params }: { params: { sessionId: string } }): Promise<Metadata> {
  const t = await getTranslations('chat');
  
  if (!validateSessionId(params.sessionId)) {
    return {
      title: t('invalid_session'),
      robots: 'noindex, nofollow',
    };
  }

  return {
    title: t('secure_chat'),
    description: t('e2e_encrypted_chat'),
    robots: 'noindex, nofollow', // チャット画面は検索エンジンにインデックスしない
    referrerPolicy: 'strict-origin-when-cross-origin',
  };
}

// チャットセッションのデータを取得（実際のアプリでは認証付きAPIから取得）
async function getChatSession(sessionId: string): Promise<{
  session: ChatSession;
  messages: SecureMessage[];
  contactName: string;
  contactAvatar?: string;
  devices: DeviceInfo[];
  currentDeviceId: string;
  currentUserId: string;
}> {
  // セッションIDの検証
  if (!validateSessionId(sessionId)) {
    throw new Error('Invalid session ID');
  }

  // 実際のアプリケーションでは、認証されたAPIからデータを取得
  // ここではモックデータを返す
  const now = new Date();
  
  const session: ChatSession = {
    id: sessionId,
    participants: ['user1', 'user2'],
    encryptionStatus: {
      isEncrypted: true,
      algorithm: 'AES-256',
      keyId: crypto.randomUUID(),
      lastRotated: new Date(now.getTime() - 12 * 60 * 60 * 1000), // 12時間前
      verified: false,
    },
    safetyNumbers: {
      'user2': {
        localNumber: '12345 67890 12345 67890 12345 67890 12345 67890 12345 67890',
        remoteNumber: '09876 54321 09876 54321 09876 54321 09876 54321 09876 54321',
        verified: false,
      },
    },
    lastActivity: new Date(now.getTime() - 5 * 60 * 1000), // 5分前
    isActive: true,
  };

  const messages: SecureMessage[] = [
    {
      id: '1',
      content: 'Hello! This is an encrypted message.',
      timestamp: new Date(now.getTime() - 30 * 60 * 1000),
      senderId: 'user2',
      receiverId: 'user1',
      encryptionStatus: session.encryptionStatus,
      delivered: true,
      read: true,
    },
    {
      id: '2',
      content: 'Hi there! I can see the encryption is working.',
      timestamp: new Date(now.getTime() - 25 * 60 * 1000),
      senderId: 'user1',
      receiverId: 'user2',
      encryptionStatus: session.encryptionStatus,
      delivered: true,
      read: true,
    },
  ];

  const devices: DeviceInfo[] = [
    {
      id: 'device1',
      name: 'iPhone 15 Pro',
      platform: 'iOS',
      lastSeen: new Date(now.getTime() - 2 * 60 * 1000),
      verified: true,
      fingerprint: 'A1B2C3D4E5F6789012345678901234567890ABCD',
    },
    {
      id: 'device2',
      name: 'MacBook Pro',
      platform: 'macOS',
      lastSeen: now,
      verified: false,
      fingerprint: 'B2C3D4E5F6789012345678901234567890ABCDE1',
    },
  ];

  return {
    session,
    messages,
    contactName: 'Alice Johnson',
    contactAvatar: '/avatars/alice.jpg',
    devices,
    currentDeviceId: 'device2',
    currentUserId: 'user1',
  };
}

interface ChatPageProps {
  params: { sessionId: string };
}

export default async function ChatPage({ params }: ChatPageProps) {
  const t = await getTranslations('chat');
  
  let chatData;
  
  try {
    chatData = await getChatSession(params.sessionId);
  } catch (error) {
    console.error('Failed to load chat session:', error);
    notFound();
  }

  const {
    session,
    messages,
    contactName,
    contactAvatar,
    devices,
    currentDeviceId,
    currentUserId,
  } = chatData;

  // メッセージ送信処理（実際のアプリでは認証付きAPIを呼び出し）
  async function handleSendMessage(content: string) {
    'use server';
    
    // 実装例：暗号化されたメッセージをサーバーに送信
    console.log('Sending encrypted message:', {
      sessionId: params.sessionId,
      content,
      timestamp: new Date().toISOString(),
    });
    
    // 実際のアプリケーションでは:
    // 1. メッセージをE2E暗号化
    // 2. サーバーに送信
    // 3. リアルタイム更新（WebSocket/Server-Sent Events）
  }

  // セキュリティ状態の更新
  async function handleRefreshStatus() {
    'use server';
    
    // 実装例：暗号化状態の確認
    console.log('Refreshing security status for session:', params.sessionId);
  }

  // 安全番号の検証
  async function handleVerifySafetyNumber() {
    'use server';
    
    console.log('Verifying safety number for session:', params.sessionId);
  }

  // 安全番号の再生成
  async function handleRegenerateSafetyNumber() {
    'use server';
    
    console.log('Regenerating safety number for session:', params.sessionId);
  }

  // デバイス検証
  async function handleVerifyDevice(deviceId: string) {
    'use server';
    
    console.log('Verifying device:', deviceId);
  }

  // デバイス取り消し
  async function handleRevokeDevice(deviceId: string) {
    'use server';
    
    console.log('Revoking device:', deviceId);
  }

  // デバイス一覧の更新
  async function handleRefreshDevices() {
    'use server';
    
    console.log('Refreshing devices for session:', params.sessionId);
  }

  return (
    <div className="h-screen">
      <SecureChatInterface
        session={session}
        messages={messages}
        currentUserId={currentUserId}
        contactName={contactName}
        contactAvatar={contactAvatar}
        onSendMessage={handleSendMessage}
        onRefreshStatus={handleRefreshStatus}
        onVerifySafetyNumber={handleVerifySafetyNumber}
        onRegenerateSafetyNumber={handleRegenerateSafetyNumber}
        onVerifyDevice={handleVerifyDevice}
        onRevokeDevice={handleRevokeDevice}
        onRefreshDevices={handleRefreshDevices}
        devices={devices}
        currentDeviceId={currentDeviceId}
      />
    </div>
  );
}

// 静的生成を無効化（チャット画面は動的コンテンツ）
export const dynamic = 'force-dynamic';
export const revalidate = 0;