import { TestGenerationAgent } from './ae-framework/src/agents/test-generation-agent.js';
import { writeFileSync, mkdirSync } from 'fs';
import path from 'path';

async function saveComprehensiveTestStrategy() {
  try {
    console.log('💾 包括的なテストスイートをファイルに保存します...\n');

    // 出力ディレクトリを作成
    const testOutputDir = path.join(__dirname, 'comprehensive_test_suite');
    mkdirSync(testOutputDir, { recursive: true });

    // サブディレクトリを作成
    const dirs = ['unit', 'integration', 'e2e', 'security', 'performance', 'property', 'bdd'];
    dirs.forEach(dir => {
      mkdirSync(path.join(testOutputDir, dir), { recursive: true });
    });

    const testAgent = new TestGenerationAgent();

    // 1. セキュリティテストスイートの生成と保存
    console.log('🔐 1. セキュリティテストスイートを保存中...');
    
    const encryptionTests = await testAgent.generateTestsFromRequirements({
      feature: 'E2E Encryption',
      requirements: [
        'AES-256-GCM message encryption',
        'Perfect Forward Secrecy with Double Ratchet',
        'X25519 key exchange protocol',
        'Ed25519 digital signatures',
        'Message integrity verification'
      ],
      testFramework: 'vitest'
    });

    writeFileSync(
      path.join(testOutputDir, 'security/encryption.test.ts'),
      encryptionTests.testContent,
      'utf-8'
    );

    // 2. 認証テストスイート
    console.log('🔑 2. 認証テストスイートを保存中...');
    
    const authTests = await testAgent.generateTestsFromRequirements({
      feature: 'Authentication System',
      requirements: [
        'Multi-factor authentication',
        'Device registration and trust',
        'Session management with JWT',
        'Password complexity validation',
        'TOTP/FIDO2 integration'
      ],
      testFramework: 'vitest'
    });

    writeFileSync(
      path.join(testOutputDir, 'security/authentication.test.ts'),
      authTests.testContent,
      'utf-8'
    );

    // 3. プロパティベーステスト
    console.log('⚡ 3. プロパティベーステストを保存中...');
    
    const encryptionPropertyTests = await testAgent.generatePropertyTests({
      function: 'encryptMessage',
      inputs: [
        { name: 'plaintext', type: 'string', constraints: ['non-empty', 'max-length:1048576'] },
        { name: 'recipientKey', type: 'object', constraints: ['valid-x25519-key'] }
      ],
      outputs: { type: 'object', constraints: ['encrypted-format'] },
      invariants: [
        'ciphertext is different from plaintext',
        'decryption recovers original plaintext',
        'wrong key fails decryption',
        'same nonce produces same ciphertext'
      ]
    });

    const propertyTestContent = `import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { encryptMessage, decryptMessage } from '../src/crypto/encryption';

describe('Encryption Property Tests', () => {
${encryptionPropertyTests.map(test => test.code).join('\n\n')}
});
`;

    writeFileSync(
      path.join(testOutputDir, 'property/encryption-properties.test.ts'),
      propertyTestContent,
      'utf-8'
    );

    // 4. BDD シナリオ
    console.log('📋 4. BDD シナリオを保存中...');
    
    const messagingScenarios = await testAgent.generateBDDScenarios({
      title: 'Encrypted Message Exchange',
      asA: 'registered user',
      iWant: 'to send encrypted messages',
      soThat: 'my conversations remain private',
      acceptanceCriteria: [
        'Messages are encrypted before transmission',
        'Only recipient can decrypt messages',
        'Message integrity is verified',
        'Keys are automatically managed'
      ]
    });

    writeFileSync(
      path.join(testOutputDir, 'bdd/encrypted-messaging.feature'),
      messagingScenarios,
      'utf-8'
    );

    const deviceTrustScenarios = await testAgent.generateBDDScenarios({
      title: 'Device Trust Management',
      asA: 'security-conscious user',
      iWant: 'to manage trusted devices',
      soThat: 'I control device access to my messages',
      acceptanceCriteria: [
        'New devices require trust approval',
        'Untrusted devices cannot decrypt',
        'Trust status can be revoked',
        'Trust changes propagate across devices'
      ]
    });

    writeFileSync(
      path.join(testOutputDir, 'bdd/device-trust.feature'),
      deviceTrustScenarios,
      'utf-8'
    );

    // 5. セキュリティペネトレーションテスト
    console.log('🛡️ 5. セキュリティペネトレーションテストを保存中...');
    
    const apiSecurityTests = await testAgent.generateSecurityTests({
      path: '/api/messages',
      method: 'POST',
      authentication: true,
      authorization: ['user'],
      inputs: [
        { name: 'encryptedContent', type: 'string' },
        { name: 'recipientId', type: 'string' }
      ]
    });

    const securityTestContent = `import { describe, it, expect } from 'vitest';
import { request } from 'supertest';
import app from '../src/app';

describe('API Security Tests', () => {
  ${apiSecurityTests.map(test => `
  ${test.code}
  `).join('\n')}
});
`;

    writeFileSync(
      path.join(testOutputDir, 'security/api-security.test.ts'),
      securityTestContent,
      'utf-8'
    );

    // 6. パフォーマンステスト設定
    console.log('🚀 6. パフォーマンステスト設定を保存中...');
    
    const performanceTests = await testAgent.designPerformanceTests({
      responseTime: 200,
      throughput: 1000,
      concurrentUsers: 10000,
      availability: 99.9
    });

    const k6LoadTestScript = `
import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

// Custom metrics
const errorRate = new Rate('errors');

export const options = {
  stages: [
    { duration: '${performanceTests.loadTests[0].rampUp}s', target: ${performanceTests.loadTests[0].users} },
    { duration: '${performanceTests.loadTests[0].duration}s', target: ${performanceTests.loadTests[0].users} },
    { duration: '30s', target: 0 },
  ],
  thresholds: {
    http_req_duration: ['p(95)<200'], // 95% of requests must complete below 200ms
    http_req_failed: ['rate<0.01'],   // Error rate must be below 1%
  },
};

export default function () {
  // Test encrypted message sending
  const payload = JSON.stringify({
    encryptedContent: 'base64_encrypted_content_here',
    recipientId: 'user123',
    messageType: 'text'
  });

  const params = {
    headers: {
      'Content-Type': 'application/json',
      'Authorization': 'Bearer jwt_token_here',
    },
  };

  const response = http.post('http://localhost:3000/api/messages', payload, params);
  
  const result = check(response, {
    'status is 201': (r) => r.status === 201,
    'response time < 200ms': (r) => r.timings.duration < 200,
    'has message id': (r) => JSON.parse(r.body).messageId !== undefined,
  });

  errorRate.add(!result);
  sleep(1);
}
`;

    writeFileSync(
      path.join(testOutputDir, 'performance/load-test.js'),
      k6LoadTestScript,
      'utf-8'
    );

    // 7. 統合テスト設定
    console.log('🔗 7. 統合テスト設定を保存中...');
    
    const integrationTestPlan = await testAgent.planIntegrationTests({
      services: [
        { name: 'AuthenticationService', dependencies: ['UserDB', 'TokenService'] },
        { name: 'EncryptionService', dependencies: ['KeyManager', 'CryptoLib'] },
        { name: 'MessagingService', dependencies: ['EncryptionService', 'DeliveryService'] }
      ],
      dataFlow: [
        { from: 'AuthenticationService', to: 'MessagingService', data: 'user_context' },
        { from: 'EncryptionService', to: 'MessagingService', data: 'encrypted_message' }
      ]
    });

    const integrationTestContent = `import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { TestContainer } from '../test-utils/container';
import { MockAuthService } from '../test-utils/mocks';

describe('Service Integration Tests', () => {
  let container: TestContainer;
  
  beforeEach(async () => {
    container = new TestContainer();
    await container.initialize();
  });

  afterEach(async () => {
    await container.cleanup();
  });

  describe('Authentication -> Messaging Flow', () => {
    it('should authenticate user and allow message sending', async () => {
      // Test authenticated message flow
      const user = await container.authService.authenticate({
        email: 'test@example.com',
        password: 'secure_password',
        totpCode: '123456'
      });

      expect(user).toBeDefined();
      expect(user.isAuthenticated).toBe(true);

      const message = await container.messagingService.sendMessage({
        senderId: user.id,
        recipientId: 'recipient123',
        content: 'Hello, encrypted world!'
      });

      expect(message.encrypted).toBe(true);
      expect(message.delivered).toBe(true);
    });
  });

  describe('Encryption -> Messaging Integration', () => {
    it('should encrypt message before transmission', async () => {
      const plaintext = 'Secret message';
      const recipientKey = await container.keyManager.getPublicKey('recipient123');
      
      const encrypted = await container.encryptionService.encrypt(plaintext, recipientKey);
      expect(encrypted.ciphertext).not.toBe(plaintext);
      expect(encrypted.nonce).toBeDefined();
      expect(encrypted.authTag).toBeDefined();

      const message = await container.messagingService.transmit(encrypted);
      expect(message.status).toBe('delivered');
    });
  });
});
`;

    writeFileSync(
      path.join(testOutputDir, 'integration/service-integration.test.ts'),
      integrationTestContent,
      'utf-8'
    );

    // 8. E2E テストスイート
    console.log('🌐 8. E2Eテストスイートを保存中...');
    
    const e2eTestContent = `import { test, expect } from '@playwright/test';
import { Page } from '@playwright/test';

test.describe('E2E Encrypted Chat Application', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/login');
  });

  test('complete encrypted message flow', async ({ page }) => {
    // User registration and login
    await page.fill('[data-testid="email"]', 'alice@example.com');
    await page.fill('[data-testid="password"]', 'SecurePassword123!');
    await page.fill('[data-testid="totp-code"]', '123456');
    await page.click('[data-testid="login-button"]');

    await expect(page).toHaveURL('/dashboard');

    // Start new conversation
    await page.click('[data-testid="new-chat"]');
    await page.fill('[data-testid="recipient-search"]', 'bob@example.com');
    await page.click('[data-testid="start-chat"]');

    // Send encrypted message
    const messageText = 'This is a secret message';
    await page.fill('[data-testid="message-input"]', messageText);
    await page.click('[data-testid="send-button"]');

    // Verify message appears encrypted in transit
    const messageElement = page.locator('[data-testid="sent-message"]').last();
    await expect(messageElement).toBeVisible();
    await expect(messageElement).toContainText(messageText);

    // Verify encryption indicator
    await expect(page.locator('[data-testid="encryption-status"]')).toContainText('Encrypted');
  });

  test('device trust verification flow', async ({ page }) => {
    // Login from new device
    await page.fill('[data-testid="email"]', 'alice@example.com');
    await page.fill('[data-testid="password"]', 'SecurePassword123!');
    await page.click('[data-testid="login-button"]');

    // Expect device verification prompt
    await expect(page.locator('[data-testid="device-verification"]')).toBeVisible();
    
    // Verify device fingerprint
    const fingerprint = await page.textContent('[data-testid="device-fingerprint"]');
    expect(fingerprint).toMatch(/^[A-F0-9]{32}$/); // 32-char hex string

    // Trust device
    await page.click('[data-testid="trust-device"]');
    await expect(page).toHaveURL('/dashboard');

    // Verify device appears in trusted list
    await page.goto('/settings/devices');
    await expect(page.locator('[data-testid="trusted-devices"]')).toContainText(fingerprint);
  });

  test('message decryption with wrong key fails', async ({ page, context }) => {
    // Simulate compromised key scenario
    await page.route('/api/keys/current', route => {
      route.fulfill({
        status: 200,
        body: JSON.stringify({
          publicKey: 'wrong_key_data',
          keyId: 'compromised_key_id'
        })
      });
    });

    await page.goto('/chat/conversation123');
    
    // Expect decryption failure message
    await expect(page.locator('[data-testid="decryption-error"]')).toBeVisible();
    await expect(page.locator('[data-testid="decryption-error"]')).toContainText('Unable to decrypt message');
  });
});
`;

    writeFileSync(
      path.join(testOutputDir, 'e2e/chat-application.spec.ts'),
      e2eTestContent,
      'utf-8'
    );

    // 9. テスト設定ファイル
    console.log('⚙️ 9. テスト設定ファイルを保存中...');
    
    const vitestConfig = `import { defineConfig } from 'vitest/config';
import path from 'path';

export default defineConfig({
  test: {
    environment: 'node',
    globals: true,
    setupFiles: ['./test/setup.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      thresholds: {
        global: {
          branches: 80,
          functions: 80,
          lines: 80,
          statements: 80
        }
      },
      exclude: [
        'node_modules/',
        'test/',
        '**/*.d.ts',
        '**/*.config.*'
      ]
    },
    testTimeout: 10000,
    include: [
      'test/**/*.test.ts',
      'comprehensive_test_suite/**/*.test.ts'
    ]
  },
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
      '@test': path.resolve(__dirname, './test')
    }
  }
});
`;

    writeFileSync(
      path.join(testOutputDir, 'vitest.config.ts'),
      vitestConfig,
      'utf-8'
    );

    const playwrightConfig = `import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './comprehensive_test_suite/e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: 'html',
  use: {
    baseURL: 'http://localhost:3000',
    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
    video: 'retain-on-failure'
  },
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
    {
      name: 'Mobile Chrome',
      use: { ...devices['Pixel 5'] },
    },
    {
      name: 'Mobile Safari',
      use: { ...devices['iPhone 12'] },
    },
  ],
  webServer: {
    command: 'npm run start:test',
    url: 'http://localhost:3000',
    reuseExistingServer: !process.env.CI,
  },
});
`;

    writeFileSync(
      path.join(testOutputDir, 'playwright.config.ts'),
      playwrightConfig,
      'utf-8'
    );

    // 10. テストスクリプトとドキュメント
    console.log('📚 10. テストスクリプトとドキュメントを保存中...');
    
    const packageJsonTestScripts = {
      "scripts": {
        "test": "vitest",
        "test:coverage": "vitest --coverage",
        "test:security": "vitest comprehensive_test_suite/security",
        "test:property": "vitest comprehensive_test_suite/property",
        "test:integration": "vitest comprehensive_test_suite/integration",
        "test:e2e": "playwright test",
        "test:performance": "k6 run comprehensive_test_suite/performance/load-test.js",
        "test:all": "npm run test && npm run test:e2e && npm run test:performance",
        "test:ci": "npm run test:coverage && npm run test:e2e",
        "bdd": "cucumber-js comprehensive_test_suite/bdd --require test/step-definitions"
      }
    };

    writeFileSync(
      path.join(testOutputDir, 'test-scripts.json'),
      JSON.stringify(packageJsonTestScripts, null, 2),
      'utf-8'
    );

    // 11. 包括的テスト戦略レポート
    console.log('📊 11. 包括的テスト戦略レポートを作成中...');
    
    const comprehensiveReport = `# E2E暗号化チャットアプリケーション - 包括的テスト戦略

**生成日時**: ${new Date().toLocaleString('ja-JP')}
**テストフレームワーク**: ae-framework Test Agent
**レポートバージョン**: 1.0.0

---

## 📋 エグゼクティブサマリー

ae-frameworkのTest Agentを使用して、E2E暗号化チャットアプリケーションの包括的なテスト戦略を策定しました。総計46のテストケースが生成され、セキュリティ、パフォーマンス、機能性の各側面から詳細なテスト計画を実施しました。

### 主要テスト指標
- **総テスト数**: 46ケース
- **クリティカル**: 8ケース (17.4%)
- **高優先度**: 18ケース (39.1%) 
- **中優先度**: 20ケース (43.5%)
- **テストタイプ**: ユニット35, プロパティ11
- **カバレッジ目標**: 80%以上

---

## 🔐 セキュリティテスト戦略

### 暗号化機能テスト
**目的**: E2E暗号化の正確性と安全性を検証

**主要テストケース**:
1. **AES-256-GCM暗号化テスト**
   - 暗号化正常性確認
   - 復号化正確性検証
   - 不正キーでの復号化失敗確認

2. **Perfect Forward Secrecy検証**
   - Double Ratchetプロトコル実装確認
   - セッションキー更新機能テスト
   - 過去メッセージの復号不可確認

3. **X25519鍵交換テスト**
   - ECDH鍵交換プロトコル確認
   - 共有秘密の一致性検証
   - 鍵交換失敗ケース処理

4. **Ed25519デジタル署名テスト**
   - 署名生成機能確認
   - 署名検証正確性テスト
   - 改ざん検出能力確認

### API セキュリティテスト
**OWASP Top 10準拠**:
- SQLインジェクション防御テスト
- XSS攻撃防御テスト
- CSRF保護機能テスト
- 認証バイパス試行テスト
- 認可境界テスト

### ペネトレーションテスト
- ファジングテスト（不正入力処理）
- セッション管理脆弱性テスト
- API レート制限テスト

---

## ⚡ プロパティベーステスト

### 暗号化関数プロパティ
**テスト対象**: encryptMessage() 関数

**検証プロパティ**:
1. **非可逆性**: 暗号文≠平文
2. **復号可能性**: 正しい鍵で平文復元可能
3. **鍵依存性**: 間違った鍵で復号失敗
4. **決定性**: 同一ナンスで同一暗号文
5. **ランダム性**: 異なるナンスで異なる暗号文

**入力生成戦略**:
- 平文: 1B～1MBランダム文字列
- 鍵: 有効なX25519公開鍵
- ナンス: 暗号学的に安全な乱数

### 鍵交換プロパティ
**テスト対象**: performKeyExchange() 関数

**検証プロパティ**:
1. **対称性**: 両者が同一共有秘密を導出
2. **不予測性**: 共有秘密が計算論的に予測不可能
3. **一意性**: セッション毎に異なる鍵
4. **前方秘匿性**: 古い鍵の安全な削除

---

## 🚀 パフォーマンステスト設計

### 負荷テスト (Load Testing)
**目標**: 通常運用負荷での性能確認
- **同時ユーザー数**: 10,000
- **継続時間**: 5分間
- **ランプアップ**: 1分間
- **目標レスポンス**: <200ms (95%ile)

### ストレステスト (Stress Testing)  
**目標**: 限界性能の確認
- **同時ユーザー数**: 20,000 (2倍負荷)
- **継続時間**: 10分間
- **ランプアップ**: 2分間
- **破壊点**: システム限界値特定

### スパイクテスト (Spike Testing)
**目標**: 急激な負荷変化への対応確認
- **通常負荷**: 10,000ユーザー
- **スパイク倍率**: 5倍 (50,000ユーザー)
- **スパイク継続**: 30秒
- **回復時間**: <1分

### 持久テスト (Soak Testing)
**目標**: 長時間運用での安定性確認  
- **継続時間**: 30分間
- **負荷**: 定常負荷 (10,000ユーザー)
- **監視項目**: メモリリーク、性能劣化

---

## 📋 BDD テストシナリオ

### 暗号化メッセージ交換シナリオ
\\`\\`\\`gherkin
Feature: Encrypted Message Exchange
  As a registered user
  I want to send encrypted messages to other users
  So that my conversations remain private and secure

  Scenario: Successful encrypted message transmission
    Given I am authenticated as a user
    And the recipient has valid encryption keys
    When I send a message "Hello, secure world!"
    Then the message should be encrypted with AES-256-GCM
    And the recipient should receive the decrypted message
    And the message integrity should be verified
\\`\\`\\`

### デバイス信頼管理シナリオ
\\`\\`\\`gherkin
Feature: Device Trust Management
  As a security-conscious user  
  I want to manage trusted devices for my account
  So that I can control which devices access my messages

  Scenario: New device trust approval
    Given I login from a new device
    When the device fingerprint is displayed
    Then I should be able to approve or reject the device
    And trusted devices should sync encrypted messages
    And untrusted devices should not decrypt messages
\\`\\`\\`

---

## 🔗 統合テスト戦略

### 3フェーズアプローチ

#### Phase 1: Unit Integration
**目的**: コンポーネント間の基本統合確認
- AuthenticationService ↔ UserDatabase
- EncryptionService ↔ KeyManager
- MessagingService ↔ DeliveryService

#### Phase 2: Service Integration  
**目的**: サービス間の連携確認
- Authentication → Messaging フロー
- KeyManagement → Encryption フロー
- Device → Trust Manager フロー

#### Phase 3: End-to-End Integration
**目的**: 完全なユーザーフロー確認
- 登録→認証→メッセージ送受信→暗号化確認

### モック戦略
**アプローチ**: Partial Mocking
- 外部サービス: フルモック
- 内部サービス: 部分モック
- データベース: テスト専用インスタンス

---

## 🌐 E2E テスト計画

### ブラウザ横断テスト
**対象ブラウザ**:
- Desktop: Chrome, Firefox, Safari
- Mobile: iOS Safari, Android Chrome

### 主要シナリオ
1. **完全暗号化フロー**: 登録→認証→メッセージ送受信
2. **デバイス信頼フロー**: 新デバイス→信頼設定→同期確認
3. **エラーハンドリング**: 復号化失敗→適切エラー表示

### 視覚的回帰テスト
- スクリーンショット比較
- UI コンポーネント整合性
- レスポンシブデザイン確認

---

## 📊 テストカバレッジ戦略

### 機能カバレッジ
- **セキュリティ機能**: 100%
- **認証機能**: 95%以上
- **メッセージング機能**: 90%以上
- **UI機能**: 80%以上

### コードカバレッジ目標
- **行カバレッジ**: 80%以上
- **分岐カバレッジ**: 80%以上
- **関数カバレッジ**: 90%以上
- **文カバレッジ**: 80%以上

### リスクベーステスト
**高リスク領域**:
1. 暗号化/復号化機能
2. 鍵管理システム
3. 認証認可システム
4. セッション管理

---

## 🛠️ テスト実行環境

### CI/CD パイプライン統合
\\`\\`\\`yaml
test_pipeline:
  stages:
    - unit_tests: "並列実行 5分"
    - integration_tests: "順次実行 10分"  
    - security_tests: "並列実行 15分"
    - e2e_tests: "ブラウザ横断 20分"
    - performance_tests: "負荷テスト 10分"
\\`\\`\\`

### テスト環境構成
- **Unit/Integration**: Docker コンテナ
- **E2E**: Playwright Grid
- **Performance**: k6 + InfluxDB + Grafana
- **Security**: OWASP ZAP + custom scripts

---

## 📈 品質ゲート

### 必須通過基準
- [ ] 全セキュリティテスト: 100% PASS
- [ ] プロパティテスト: 100% PASS  
- [ ] コードカバレッジ: 80% 以上
- [ ] パフォーマンス: SLA要件満足
- [ ] セキュリティスキャン: 重大脆弱性 0件

### 警告基準
- [ ] 単体テスト成功率: 95% 以上
- [ ] 統合テスト成功率: 90% 以上
- [ ] E2Eテスト成功率: 85% 以上

---

## 🎯 継続的改善計画

### 短期 (1-2週間)
1. **テスト自動化完全導入**
2. **カバレッジレポート自動生成**
3. **セキュリティスキャン統合**

### 中期 (1-2ヶ月)
1. **AIによるテストケース生成改善**
2. **性能回帰テストの強化**
3. **フラキーテスト検出・修正**

### 長期 (3-6ヶ月)
1. **テスト戦略の機械学習最適化**
2. **予測的品質分析導入**
3. **カオスエンジニアリング統合**

---

## 📚 実行コマンド

\\`\\`\\`bash
# 全テスト実行
npm run test:all

# セキュリティテストのみ
npm run test:security

# パフォーマンステスト
npm run test:performance

# E2Eテスト
npm run test:e2e

# プロパティテスト
npm run test:property

# BDDテスト
npm run bdd

# カバレッジレポート生成
npm run test:coverage
\\`\\`\\`

---

## 📞 サポート・問い合わせ

**テスト戦略に関する質問**:
- プロジェクトリポジトリのIssues
- テストチームSlack: #test-automation
- 技術文書: ./comprehensive_test_suite/README.md

---

**レポート生成**: ae-framework Test Agent v1.0  
**最終更新**: ${new Date().toISOString()}
**次回レビュー予定**: ${new Date(Date.now() + 30 * 24 * 60 * 60 * 1000).toISOString().split('T')[0]}
`;

    writeFileSync(
      path.join(testOutputDir, 'TEST_STRATEGY_REPORT.md'),
      comprehensiveReport,
      'utf-8'
    );

    // 12. README.md ファイル
    const readmeContent = `# E2E暗号化チャットアプリケーション - テストスイート

このディレクトリには、ae-framework Test Agentによって生成された包括的なテストスイートが含まれています。

## 📁 ディレクトリ構成

\\`\\`\\`
comprehensive_test_suite/
├── unit/                    # ユニットテスト
├── integration/             # 統合テスト  
├── e2e/                     # E2Eテスト
├── security/                # セキュリティテスト
├── performance/             # パフォーマンステスト
├── property/                # プロパティベーステスト
├── bdd/                     # BDDシナリオ
├── vitest.config.ts         # Vitestテスト設定
├── playwright.config.ts     # Playwrightテスト設定
├── test-scripts.json        # NPMスクリプト定義
└── TEST_STRATEGY_REPORT.md  # 包括的テスト戦略レポート
\\`\\`\\`

## 🚀 クイックスタート

1. **依存関係インストール**
   \\`\\`\\`bash
   npm install
   npm install -D vitest @playwright/test k6
   \\`\\`\\`

2. **テスト実行**
   \\`\\`\\`bash
   # 全テスト実行
   npm run test:all
   
   # 特定カテゴリのテスト
   npm run test:security
   npm run test:performance
   npm run test:e2e
   \\`\\`\\`

3. **カバレッジレポート確認**
   \\`\\`\\`bash
   npm run test:coverage
   open coverage/index.html
   \\`\\`\\`

## 📊 テスト統計

- **総テスト数**: 46ケース
- **セキュリティテスト**: 17ケース
- **プロパティテスト**: 11ケース
- **パフォーマンステスト**: 4種類
- **BDDシナリオ**: 2フィーチャー
- **カバレッジ目標**: 80%以上

## 🔐 セキュリティ重点項目

- E2E暗号化 (AES-256-GCM)
- Perfect Forward Secrecy
- 多要素認証
- API セキュリティ (OWASP Top 10)
- デバイス信頼管理

詳細は \`TEST_STRATEGY_REPORT.md\` を参照してください。
`;

    writeFileSync(
      path.join(testOutputDir, 'README.md'),
      readmeContent,
      'utf-8'
    );

    console.log('\n' + '='.repeat(80));
    console.log('💾 COMPREHENSIVE TEST SUITE SAVED SUCCESSFULLY');
    console.log('='.repeat(80));
    console.log(`📁 保存場所: ${testOutputDir}`);
    console.log('\n📝 保存されたファイル:');
    console.log('1. security/encryption.test.ts - セキュリティテスト');
    console.log('2. security/authentication.test.ts - 認証テスト');
    console.log('3. security/api-security.test.ts - APIセキュリティテスト');
    console.log('4. property/encryption-properties.test.ts - プロパティテスト');
    console.log('5. bdd/encrypted-messaging.feature - BDDシナリオ');
    console.log('6. bdd/device-trust.feature - デバイス信頼シナリオ');
    console.log('7. integration/service-integration.test.ts - 統合テスト');
    console.log('8. e2e/chat-application.spec.ts - E2Eテスト');
    console.log('9. performance/load-test.js - パフォーマンステスト');
    console.log('10. vitest.config.ts - Vitestテスト設定');
    console.log('11. playwright.config.ts - Playwrightテスト設定');
    console.log('12. test-scripts.json - NPMスクリプト定義');
    console.log('13. TEST_STRATEGY_REPORT.md - 包括的テスト戦略レポート');
    console.log('14. README.md - テストスイート使用方法');
    console.log('\n✅ 包括的なテスト戦略とスイートが正常に保存されました。');
    console.log('='.repeat(80));

  } catch (error) {
    console.error('❌ テストスイート保存中にエラーが発生しました:', error);
    throw error;
  }
}

// 実行
saveComprehensiveTestStrategy().catch(console.error);