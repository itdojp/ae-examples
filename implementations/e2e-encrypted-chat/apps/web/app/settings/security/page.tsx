import { Metadata } from 'next';
import { getTranslations } from 'next-intl/server';
import { 
  Shield, ShieldCheck, Key, Smartphone, RefreshCw, Download, 
  AlertTriangle, Clock, Settings 
} from 'lucide-react';
import { EncryptionStatusIndicator } from '@/components/secure/EncryptionStatusIndicator';
import type { EncryptionStatus, SecurityMetrics } from '@/types/security';

export async function generateMetadata(): Promise<Metadata> {
  const t = await getTranslations('settings');
  
  return {
    title: t('security_settings'),
    description: t('manage_security_preferences'),
    robots: 'noindex, nofollow',
    referrerPolicy: 'strict-origin-when-cross-origin',
  };
}

// セキュリティ設定データの取得
async function getSecuritySettings(): Promise<{
  encryptionStatus: EncryptionStatus;
  securityMetrics: SecurityMetrics;
  settings: {
    autoKeyRotation: boolean;
    requireDeviceVerification: boolean;
    allowScreenshots: boolean;
    sessionTimeout: number;
    backupEnabled: boolean;
  };
}> {
  const now = new Date();
  
  return {
    encryptionStatus: {
      isEncrypted: true,
      algorithm: 'AES-256',
      keyId: crypto.randomUUID(),
      lastRotated: new Date(now.getTime() - 8 * 60 * 60 * 1000), // 8時間前
      verified: true,
    },
    securityMetrics: {
      encryptionLatency: 12,
      keyRotationDue: false,
      verificationStatus: 'verified',
      lastSecurityCheck: new Date(now.getTime() - 30 * 60 * 1000), // 30分前
    },
    settings: {
      autoKeyRotation: true,
      requireDeviceVerification: true,
      allowScreenshots: false,
      sessionTimeout: 3600000, // 1時間
      backupEnabled: true,
    },
  };
}

export default async function SecuritySettingsPage() {
  const t = await getTranslations('settings');
  const data = await getSecuritySettings();
  
  const { encryptionStatus, securityMetrics, settings } = data;

  // 設定更新処理
  async function updateSetting(key: string, value: boolean | number) {
    'use server';
    
    console.log('Updating security setting:', { key, value });
    
    // 実際のアプリケーションでは:
    // 1. 設定の検証
    // 2. データベースの更新
    // 3. セキュリティ監査ログの記録
    // 4. 必要に応じて暗号化設定の再構成
  }

  // キー手動回転
  async function rotateKeys() {
    'use server';
    
    console.log('Manually rotating encryption keys');
    
    // 実際のアプリケーションでは:
    // 1. 新しい暗号化キーの生成
    // 2. 既存のセッションキーの更新
    // 3. 相手への通知
    // 4. セキュリティ監査ログの記録
  }

  // セキュリティ監査の実行
  async function runSecurityAudit() {
    'use server';
    
    console.log('Running security audit');
    
    // 実際のアプリケーションでは:
    // 1. デバイスの整合性チェック
    // 2. 暗号化状態の検証
    // 3. 不審なアクティビティの検出
    // 4. セキュリティレポートの生成
  }

  // バックアップの作成
  async function createBackup() {
    'use server';
    
    console.log('Creating encrypted backup');
    
    // 実際のアプリケーションでは:
    // 1. 暗号化されたバックアップの作成
    // 2. セキュアなストレージへの保存
    // 3. バックアップの整合性検証
    // 4. ユーザーへの通知
  }

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-gray-900">
      <div className="max-w-4xl mx-auto py-12 px-4 sm:px-6 lg:px-8">
        {/* ヘッダー */}
        <div className="mb-8">
          <div className="flex items-center gap-3 mb-4">
            <Shield className="h-8 w-8 text-blue-600" />
            <h1 className="text-3xl font-bold text-gray-900 dark:text-white">
              {t('security_settings')}
            </h1>
          </div>
          <p className="text-gray-600 dark:text-gray-400">
            {t('security_settings_description')}
          </p>
        </div>

        <div className="space-y-8">
          {/* 暗号化ステータス */}
          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
              <ShieldCheck className="h-5 w-5 text-green-600" />
              {t('encryption_status')}
            </h2>
            
            <div className="space-y-4">
              <EncryptionStatusIndicator
                encryptionStatus={encryptionStatus}
                showDetails={true}
                size="lg"
              />
              
              <div className="grid grid-cols-1 md:grid-cols-3 gap-4 mt-6">
                <div className="bg-gray-50 dark:bg-gray-700 p-4 rounded-lg">
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('encryption_algorithm')}
                  </div>
                  <div className="text-lg font-semibold text-gray-900 dark:text-white">
                    {encryptionStatus.algorithm}
                  </div>
                </div>
                
                <div className="bg-gray-50 dark:bg-gray-700 p-4 rounded-lg">
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('key_rotation')}
                  </div>
                  <div className="text-lg font-semibold text-gray-900 dark:text-white">
                    {encryptionStatus.lastRotated.toLocaleDateString()}
                  </div>
                </div>
                
                <div className="bg-gray-50 dark:bg-gray-700 p-4 rounded-lg">
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('verification_status')}
                  </div>
                  <div className="text-lg font-semibold text-green-600 dark:text-green-400">
                    {encryptionStatus.verified ? t('verified') : t('unverified')}
                  </div>
                </div>
              </div>
            </div>
          </div>

          {/* セキュリティメトリクス */}
          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
              <Settings className="h-5 w-5 text-blue-600" />
              {t('security_metrics')}
            </h2>
            
            <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
              <div className="bg-green-50 dark:bg-green-900/20 p-4 rounded-lg border border-green-200 dark:border-green-800">
                <div className="text-sm text-green-700 dark:text-green-300">
                  {t('encryption_latency')}
                </div>
                <div className="text-2xl font-bold text-green-800 dark:text-green-200">
                  {securityMetrics.encryptionLatency}ms
                </div>
              </div>
              
              <div className={`p-4 rounded-lg border ${
                securityMetrics.keyRotationDue 
                  ? 'bg-yellow-50 dark:bg-yellow-900/20 border-yellow-200 dark:border-yellow-800'
                  : 'bg-gray-50 dark:bg-gray-700 border-gray-200 dark:border-gray-600'
              }`}>
                <div className={`text-sm ${
                  securityMetrics.keyRotationDue
                    ? 'text-yellow-700 dark:text-yellow-300'
                    : 'text-gray-700 dark:text-gray-300'
                }`}>
                  {t('key_rotation_status')}
                </div>
                <div className={`text-2xl font-bold ${
                  securityMetrics.keyRotationDue
                    ? 'text-yellow-800 dark:text-yellow-200'
                    : 'text-gray-800 dark:text-gray-200'
                }`}>
                  {securityMetrics.keyRotationDue ? t('due') : t('current')}
                </div>
              </div>
              
              <div className="bg-blue-50 dark:bg-blue-900/20 p-4 rounded-lg border border-blue-200 dark:border-blue-800">
                <div className="text-sm text-blue-700 dark:text-blue-300">
                  {t('verification_status')}
                </div>
                <div className="text-2xl font-bold text-blue-800 dark:text-blue-200 capitalize">
                  {t(securityMetrics.verificationStatus)}
                </div>
              </div>
              
              <div className="bg-gray-50 dark:bg-gray-700 p-4 rounded-lg border border-gray-200 dark:border-gray-600">
                <div className="text-sm text-gray-700 dark:text-gray-300">
                  {t('last_security_check')}
                </div>
                <div className="text-sm font-bold text-gray-800 dark:text-gray-200">
                  {securityMetrics.lastSecurityCheck.toLocaleTimeString()}
                </div>
              </div>
            </div>
          </div>

          {/* セキュリティ設定 */}
          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <h2 className="text-lg font-semibold mb-6 flex items-center gap-2">
              <Key className="h-5 w-5 text-blue-600" />
              {t('security_preferences')}
            </h2>
            
            <div className="space-y-6">
              {/* 自動キー回転 */}
              <div className="flex items-center justify-between py-4 border-b border-gray-200 dark:border-gray-700">
                <div>
                  <h3 className="font-medium text-gray-900 dark:text-white">
                    {t('auto_key_rotation')}
                  </h3>
                  <p className="text-sm text-gray-600 dark:text-gray-400">
                    {t('auto_key_rotation_description')}
                  </p>
                </div>
                <label className="relative inline-flex items-center cursor-pointer">
                  <input
                    type="checkbox"
                    defaultChecked={settings.autoKeyRotation}
                    className="sr-only peer"
                    onChange={(e) => updateSetting('autoKeyRotation', e.target.checked)}
                  />
                  <div className="w-11 h-6 bg-gray-200 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-gray-700 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>
                </label>
              </div>

              {/* デバイス検証要求 */}
              <div className="flex items-center justify-between py-4 border-b border-gray-200 dark:border-gray-700">
                <div>
                  <h3 className="font-medium text-gray-900 dark:text-white">
                    {t('require_device_verification')}
                  </h3>
                  <p className="text-sm text-gray-600 dark:text-gray-400">
                    {t('require_device_verification_description')}
                  </p>
                </div>
                <label className="relative inline-flex items-center cursor-pointer">
                  <input
                    type="checkbox"
                    defaultChecked={settings.requireDeviceVerification}
                    className="sr-only peer"
                    onChange={(e) => updateSetting('requireDeviceVerification', e.target.checked)}
                  />
                  <div className="w-11 h-6 bg-gray-200 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-gray-700 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>
                </label>
              </div>

              {/* スクリーンショット許可 */}
              <div className="flex items-center justify-between py-4 border-b border-gray-200 dark:border-gray-700">
                <div>
                  <h3 className="font-medium text-gray-900 dark:text-white">
                    {t('allow_screenshots')}
                  </h3>
                  <p className="text-sm text-gray-600 dark:text-gray-400">
                    {t('allow_screenshots_description')}
                  </p>
                </div>
                <label className="relative inline-flex items-center cursor-pointer">
                  <input
                    type="checkbox"
                    defaultChecked={settings.allowScreenshots}
                    className="sr-only peer"
                    onChange={(e) => updateSetting('allowScreenshots', e.target.checked)}
                  />
                  <div className="w-11 h-6 bg-gray-200 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-gray-700 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>
                </label>
              </div>

              {/* バックアップ設定 */}
              <div className="flex items-center justify-between py-4">
                <div>
                  <h3 className="font-medium text-gray-900 dark:text-white">
                    {t('encrypted_backups')}
                  </h3>
                  <p className="text-sm text-gray-600 dark:text-gray-400">
                    {t('encrypted_backups_description')}
                  </p>
                </div>
                <label className="relative inline-flex items-center cursor-pointer">
                  <input
                    type="checkbox"
                    defaultChecked={settings.backupEnabled}
                    className="sr-only peer"
                    onChange={(e) => updateSetting('backupEnabled', e.target.checked)}
                  />
                  <div className="w-11 h-6 bg-gray-200 peer-focus:outline-none peer-focus:ring-4 peer-focus:ring-blue-300 dark:peer-focus:ring-blue-800 rounded-full peer dark:bg-gray-700 peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all dark:border-gray-600 peer-checked:bg-blue-600"></div>
                </label>
              </div>
            </div>
          </div>

          {/* セキュリティアクション */}
          <div className="bg-white dark:bg-gray-800 shadow rounded-lg p-6">
            <h2 className="text-lg font-semibold mb-6 flex items-center gap-2">
              <Smartphone className="h-5 w-5 text-blue-600" />
              {t('security_actions')}
            </h2>
            
            <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
              <button
                onClick={rotateKeys}
                className="flex items-center gap-3 p-4 border border-gray-300 dark:border-gray-600 rounded-lg hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
              >
                <RefreshCw className="h-5 w-5 text-blue-600" />
                <div className="text-left">
                  <div className="font-medium text-gray-900 dark:text-white">
                    {t('rotate_encryption_keys')}
                  </div>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('rotate_keys_description')}
                  </div>
                </div>
              </button>
              
              <button
                onClick={createBackup}
                className="flex items-center gap-3 p-4 border border-gray-300 dark:border-gray-600 rounded-lg hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
              >
                <Download className="h-5 w-5 text-green-600" />
                <div className="text-left">
                  <div className="font-medium text-gray-900 dark:text-white">
                    {t('create_backup')}
                  </div>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('create_backup_description')}
                  </div>
                </div>
              </button>
              
              <button
                onClick={runSecurityAudit}
                className="flex items-center gap-3 p-4 border border-gray-300 dark:border-gray-600 rounded-lg hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
              >
                <Shield className="h-5 w-5 text-purple-600" />
                <div className="text-left">
                  <div className="font-medium text-gray-900 dark:text-white">
                    {t('run_security_audit')}
                  </div>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('security_audit_description')}
                  </div>
                </div>
              </button>
              
              <a
                href="/help/security"
                className="flex items-center gap-3 p-4 border border-gray-300 dark:border-gray-600 rounded-lg hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
              >
                <AlertTriangle className="h-5 w-5 text-orange-600" />
                <div className="text-left">
                  <div className="font-medium text-gray-900 dark:text-white">
                    {t('security_help')}
                  </div>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {t('security_help_description')}
                  </div>
                </div>
              </a>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}

// 静的生成を無効化（認証が必要なページ）
export const dynamic = 'force-dynamic';
export const revalidate = 0;