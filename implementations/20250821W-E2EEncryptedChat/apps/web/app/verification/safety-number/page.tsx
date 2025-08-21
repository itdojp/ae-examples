import { Metadata } from 'next';
import { getTranslations } from 'next-intl/server';
import { redirect } from 'next/navigation';
import { SafetyNumberVerification } from '@/components/secure/SafetyNumberVerification';
import type { SafetyNumber } from '@/types/security';

export async function generateMetadata(): Promise<Metadata> {
  const t = await getTranslations('verification');
  
  return {
    title: t('safety_number_verification'),
    description: t('verify_contact_identity'),
    robots: 'noindex, nofollow',
    referrerPolicy: 'strict-origin-when-cross-origin',
  };
}

// 安全番号データの取得（実際のアプリでは認証済みユーザーのデータを取得）
async function getSafetyNumberData(searchParams: URLSearchParams): Promise<{
  safetyNumber: SafetyNumber;
  contactName: string;
  contactId: string;
}> {
  const contactId = searchParams.get('contact');
  
  if (!contactId) {
    throw new Error('Contact ID is required');
  }

  // 実際のアプリケーションでは、認証されたAPIからデータを取得
  const safetyNumber: SafetyNumber = {
    localNumber: '12345 67890 12345 67890 12345 67890 12345 67890 12345 67890',
    remoteNumber: '09876 54321 09876 54321 09876 54321 09876 54321 09876 54321',
    verified: false,
    lastVerified: undefined,
  };

  return {
    safetyNumber,
    contactName: 'Alice Johnson',
    contactId,
  };
}

interface VerificationPageProps {
  searchParams: { [key: string]: string | string[] | undefined };
}

export default async function SafetyNumberVerificationPage({ 
  searchParams 
}: VerificationPageProps) {
  const t = await getTranslations('verification');
  const urlSearchParams = new URLSearchParams();
  
  // URLパラメータの構築
  Object.entries(searchParams).forEach(([key, value]) => {
    if (typeof value === 'string') {
      urlSearchParams.set(key, value);
    } else if (Array.isArray(value)) {
      urlSearchParams.set(key, value[0]);
    }
  });

  let verificationData;
  
  try {
    verificationData = await getSafetyNumberData(urlSearchParams);
  } catch (error) {
    console.error('Failed to load safety number data:', error);
    redirect('/chat');
  }

  const { safetyNumber, contactName, contactId } = verificationData;

  // 安全番号検証処理
  async function handleVerification() {
    'use server';
    
    console.log('Verifying safety number for contact:', contactId);
    
    // 実際のアプリケーションでは:
    // 1. ユーザーの確認を得る
    // 2. 安全番号をマークとして検証済みに設定
    // 3. セキュリティ監査ログに記録
    // 4. 対応するチャットセッションのステータスを更新
    
    // 検証後はチャット画面にリダイレクト
    redirect(`/chat/${contactId}`);
  }

  // 安全番号再生成処理
  async function handleRegeneration() {
    'use server';
    
    console.log('Regenerating safety number for contact:', contactId);
    
    // 実際のアプリケーションでは:
    // 1. 新しい安全番号を生成
    // 2. 相手に通知
    // 3. 既存の検証状態をリセット
    // 4. セキュリティ監査ログに記録
  }

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-gray-900 py-12 px-4 sm:px-6 lg:px-8">
      <div className="max-w-md mx-auto">
        {/* ヘッダー */}
        <div className="text-center mb-8">
          <h1 className="text-3xl font-bold text-gray-900 dark:text-white">
            {t('safety_number_verification')}
          </h1>
          <p className="mt-2 text-gray-600 dark:text-gray-400">
            {t('verify_contact_identity_description')}
          </p>
        </div>

        {/* セキュリティ警告 */}
        <div className="mb-6 p-4 bg-blue-50 dark:bg-blue-900/20 border border-blue-200 dark:border-blue-800 rounded-lg">
          <h2 className="text-sm font-medium text-blue-800 dark:text-blue-200 mb-2">
            {t('security_notice')}
          </h2>
          <ul className="text-sm text-blue-700 dark:text-blue-300 space-y-1">
            <li>• {t('verify_in_person_recommended')}</li>
            <li>• {t('compare_numbers_carefully')}</li>
            <li>• {t('contact_if_mismatch')}</li>
          </ul>
        </div>

        {/* 検証コンポーネント */}
        <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
          <SafetyNumberVerification
            safetyNumber={safetyNumber}
            contactName={contactName}
            onVerify={handleVerification}
            onRegenerate={handleRegeneration}
            isOpen={true}
            onClose={() => redirect('/chat')}
          />
        </div>

        {/* 追加情報 */}
        <div className="mt-6 text-center">
          <p className="text-sm text-gray-600 dark:text-gray-400">
            {t('verification_help_text')}{' '}
            <a 
              href="/help/safety-numbers"
              className="text-blue-600 hover:text-blue-700 dark:text-blue-400 dark:hover:text-blue-300"
            >
              {t('learn_more')}
            </a>
          </p>
        </div>
      </div>
    </div>
  );
}

// 静的生成を無効化（認証が必要なページ）
export const dynamic = 'force-dynamic';
export const revalidate = 0;