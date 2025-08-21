import { Metadata } from 'next';
import { getTranslations } from 'next-intl/server';
import { DeviceVerificationDialog } from '@/components/secure/DeviceVerificationDialog';
import type { DeviceInfo } from '@/types/security';

export async function generateMetadata(): Promise<Metadata> {
  const t = await getTranslations('devices');
  
  return {
    title: t('device_management'),
    description: t('manage_trusted_devices'),
    robots: 'noindex, nofollow',
    referrerPolicy: 'strict-origin-when-cross-origin',
  };
}

// デバイス一覧の取得
async function getDevices(): Promise<{
  devices: DeviceInfo[];
  currentDeviceId: string;
}> {
  const now = new Date();
  
  const devices: DeviceInfo[] = [
    {
      id: 'device1',
      name: 'iPhone 15 Pro',
      platform: 'iOS',
      lastSeen: new Date(now.getTime() - 2 * 60 * 1000), // 2分前
      verified: true,
      fingerprint: 'A1B2C3D4E5F6789012345678901234567890ABCD',
    },
    {
      id: 'device2',
      name: 'MacBook Pro',
      platform: 'macOS',
      lastSeen: now,
      verified: true,
      fingerprint: 'B2C3D4E5F6789012345678901234567890ABCDE1',
    },
    {
      id: 'device3',
      name: 'iPad Air',
      platform: 'iPad',
      lastSeen: new Date(now.getTime() - 24 * 60 * 60 * 1000), // 1日前
      verified: false,
      fingerprint: 'C3D4E5F6789012345678901234567890ABCDEF12',
    },
    {
      id: 'device4',
      name: 'Windows Desktop',
      platform: 'Windows',
      lastSeen: new Date(now.getTime() - 7 * 24 * 60 * 60 * 1000), // 1週間前
      verified: false,
      fingerprint: 'D4E5F6789012345678901234567890ABCDEF123',
    },
  ];

  return {
    devices,
    currentDeviceId: 'device2', // MacBook Pro
  };
}

export default async function DevicesPage() {
  const t = await getTranslations('devices');
  const { devices, currentDeviceId } = await getDevices();

  // デバイス検証処理
  async function handleVerifyDevice(deviceId: string) {
    'use server';
    
    console.log('Verifying device:', deviceId);
    
    // 実際のアプリケーションでは:
    // 1. デバイスの身元確認
    // 2. 検証ステータスの更新
    // 3. セキュリティキーの共有
    // 4. セキュリティ監査ログの記録
  }

  // デバイス取り消し処理
  async function handleRevokeDevice(deviceId: string) {
    'use server';
    
    console.log('Revoking device:', deviceId);
    
    // 実際のアプリケーションでは:
    // 1. デバイスアクセスの取り消し
    // 2. セッションの無効化
    // 3. セキュリティキーの削除
    // 4. ユーザーへの通知
    // 5. セキュリティ監査ログの記録
  }

  // デバイス一覧の更新
  async function handleRefreshDevices() {
    'use server';
    
    console.log('Refreshing device list');
    
    // 実際のアプリケーションでは:
    // 1. 最新のデバイス情報を取得
    // 2. オフラインデバイスの検出
    // 3. セキュリティ状態の確認
    // 4. UI状態の更新
  }

  // 統計の計算
  const stats = {
    total: devices.length,
    verified: devices.filter(d => d.verified).length,
    unverified: devices.filter(d => !d.verified).length,
    active: devices.filter(d => {
      const hoursSinceLastSeen = (Date.now() - d.lastSeen.getTime()) / (1000 * 60 * 60);
      return hoursSinceLastSeen < 24;
    }).length,
  };

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-gray-900">
      <div className="max-w-6xl mx-auto py-12 px-4 sm:px-6 lg:px-8">
        {/* ヘッダー */}
        <div className="mb-8">
          <h1 className="text-3xl font-bold text-gray-900 dark:text-white">
            {t('device_management')}
          </h1>
          <p className="mt-2 text-gray-600 dark:text-gray-400">
            {t('device_management_description')}
          </p>
        </div>

        {/* 統計カード */}
        <div className="grid grid-cols-1 md:grid-cols-4 gap-6 mb-8">
          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <div className="w-8 h-8 bg-blue-100 dark:bg-blue-900/30 rounded-md flex items-center justify-center">
                  <span className="text-blue-600 dark:text-blue-400 font-semibold">
                    {stats.total}
                  </span>
                </div>
              </div>
              <div className="ml-4">
                <div className="text-sm font-medium text-gray-500 dark:text-gray-400">
                  {t('total_devices')}
                </div>
                <div className="text-2xl font-bold text-gray-900 dark:text-white">
                  {stats.total}
                </div>
              </div>
            </div>
          </div>

          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <div className="w-8 h-8 bg-green-100 dark:bg-green-900/30 rounded-md flex items-center justify-center">
                  <span className="text-green-600 dark:text-green-400 font-semibold">
                    {stats.verified}
                  </span>
                </div>
              </div>
              <div className="ml-4">
                <div className="text-sm font-medium text-gray-500 dark:text-gray-400">
                  {t('verified_devices')}
                </div>
                <div className="text-2xl font-bold text-green-600 dark:text-green-400">
                  {stats.verified}
                </div>
              </div>
            </div>
          </div>

          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <div className="w-8 h-8 bg-yellow-100 dark:bg-yellow-900/30 rounded-md flex items-center justify-center">
                  <span className="text-yellow-600 dark:text-yellow-400 font-semibold">
                    {stats.unverified}
                  </span>
                </div>
              </div>
              <div className="ml-4">
                <div className="text-sm font-medium text-gray-500 dark:text-gray-400">
                  {t('unverified_devices')}
                </div>
                <div className="text-2xl font-bold text-yellow-600 dark:text-yellow-400">
                  {stats.unverified}
                </div>
              </div>
            </div>
          </div>

          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <div className="w-8 h-8 bg-purple-100 dark:bg-purple-900/30 rounded-md flex items-center justify-center">
                  <span className="text-purple-600 dark:text-purple-400 font-semibold">
                    {stats.active}
                  </span>
                </div>
              </div>
              <div className="ml-4">
                <div className="text-sm font-medium text-gray-500 dark:text-gray-400">
                  {t('active_devices')}
                </div>
                <div className="text-2xl font-bold text-purple-600 dark:text-purple-400">
                  {stats.active}
                </div>
              </div>
            </div>
          </div>
        </div>

        {/* セキュリティ警告 */}
        {stats.unverified > 0 && (
          <div className="mb-8 bg-yellow-50 dark:bg-yellow-900/20 border-l-4 border-yellow-400 p-4">
            <div className="flex">
              <div className="flex-shrink-0">
                <svg className="h-5 w-5 text-yellow-400" viewBox="0 0 20 20" fill="currentColor">
                  <path fillRule="evenodd" d="M8.257 3.099c.765-1.36 2.722-1.36 3.486 0l5.58 9.92c.75 1.334-.213 2.98-1.742 2.98H4.42c-1.53 0-2.493-1.646-1.743-2.98l5.58-9.92zM11 13a1 1 0 11-2 0 1 1 0 012 0zm-1-8a1 1 0 00-1 1v3a1 1 0 002 0V6a1 1 0 00-1-1z" clipRule="evenodd" />
                </svg>
              </div>
              <div className="ml-3">
                <p className="text-sm text-yellow-700 dark:text-yellow-200">
                  {t('unverified_devices_security_warning', { count: stats.unverified })}
                </p>
              </div>
            </div>
          </div>
        )}

        {/* デバイス管理インターフェース */}
        <div className="bg-white dark:bg-gray-800 shadow rounded-lg">
          <DeviceVerificationDialog
            devices={devices}
            currentDeviceId={currentDeviceId}
            onVerifyDevice={handleVerifyDevice}
            onRevokeDevice={handleRevokeDevice}
            onRefreshDevices={handleRefreshDevices}
            isOpen={true}
            onClose={() => {}} // スタンドアロンページでは閉じる動作は不要
            className="border-0 shadow-none bg-transparent max-h-none overflow-visible"
          />
        </div>

        {/* セキュリティのベストプラクティス */}
        <div className="mt-8 bg-blue-50 dark:bg-blue-900/20 border border-blue-200 dark:border-blue-800 rounded-lg p-6">
          <h3 className="text-lg font-semibold text-blue-900 dark:text-blue-100 mb-4">
            {t('security_best_practices')}
          </h3>
          <ul className="space-y-2 text-blue-800 dark:text-blue-200">
            <li className="flex items-start gap-2">
              <span className="text-blue-500 mt-1">•</span>
              <span className="text-sm">{t('verify_new_devices_immediately')}</span>
            </li>
            <li className="flex items-start gap-2">
              <span className="text-blue-500 mt-1">•</span>
              <span className="text-sm">{t('revoke_unused_devices_regularly')}</span>
            </li>
            <li className="flex items-start gap-2">
              <span className="text-blue-500 mt-1">•</span>
              <span className="text-sm">{t('monitor_device_activity')}</span>
            </li>
            <li className="flex items-start gap-2">
              <span className="text-blue-500 mt-1">•</span>
              <span className="text-sm">{t('report_suspicious_devices')}</span>
            </li>
          </ul>
        </div>
      </div>
    </div>
  );
}

// 静的生成を無効化（認証が必要なページ）
export const dynamic = 'force-dynamic';
export const revalidate = 0;