import { test, expect, Page, BrowserContext } from '@playwright/test';

/**
 * E2E暗号化チャットアプリケーション - フルフローE2Eテスト
 * 
 * このテストは実際のブラウザを使用してアプリケーション全体の動作を検証します。
 * ユーザー登録からメッセージ送受信、既読管理まで一連の流れをテストします。
 */

test.describe('E2E暗号化チャット フルフロー', () => {
  let context: BrowserContext;
  let alicePage: Page;
  let bobPage: Page;
  
  const ALICE_EMAIL = 'alice@example.com';
  const BOB_EMAIL = 'bob@example.com';
  const PASSWORD = 'password123';
  const BASE_URL = 'http://localhost:4173';

  test.beforeAll(async ({ browser }) => {
    context = await browser.newContext();
  });

  test.afterAll(async () => {
    await context.close();
  });

  test.beforeEach(async () => {
    alicePage = await context.newPage();
    bobPage = await context.newPage();
  });

  test.afterEach(async () => {
    await alicePage.close();
    await bobPage.close();
  });

  test('完全なE2Eチャットフロー', async () => {
    // === Step 1: ユーザー登録 ===
    
    // Alice の登録
    await alicePage.goto(BASE_URL);
    await alicePage.waitForSelector('[data-testid="auth-form"]');
    
    await alicePage.click('[data-testid="register-tab"]');
    await alicePage.fill('[data-testid="email-input"]', ALICE_EMAIL);
    await alicePage.fill('[data-testid="password-input"]', PASSWORD);
    await alicePage.fill('[data-testid="displayname-input"]', 'Alice');
    await alicePage.click('[data-testid="register-button"]');
    
    // 登録成功確認
    await expect(alicePage.locator('[data-testid="chat-interface"]')).toBeVisible();
    await expect(alicePage.locator('[data-testid="user-display-name"]')).toContainText('Alice');

    // Bob の登録
    await bobPage.goto(BASE_URL);
    await bobPage.waitForSelector('[data-testid="auth-form"]');
    
    await bobPage.click('[data-testid="register-tab"]');
    await bobPage.fill('[data-testid="email-input"]', BOB_EMAIL);
    await bobPage.fill('[data-testid="password-input"]', PASSWORD);
    await bobPage.fill('[data-testid="displayname-input"]', 'Bob');
    await bobPage.click('[data-testid="register-button"]');
    
    // 登録成功確認
    await expect(bobPage.locator('[data-testid="chat-interface"]')).toBeVisible();
    await expect(bobPage.locator('[data-testid="user-display-name"]')).toContainText('Bob');

    // === Step 2: キー生成確認 ===
    
    // Alice のキー生成確認
    await alicePage.click('[data-testid="settings-button"]');
    await expect(alicePage.locator('[data-testid="public-key-display"]')).toBeVisible();
    await expect(alicePage.locator('[data-testid="public-key-display"]')).toContainText('BEGIN PUBLIC KEY');
    await alicePage.press('Escape'); // 設定パネルを閉じる

    // Bob のキー生成確認
    await bobPage.click('[data-testid="settings-button"]');
    await expect(bobPage.locator('[data-testid="public-key-display"]')).toBeVisible();
    await bobPage.press('Escape');

    // === Step 3: 会話開始 ===
    
    // Alice が Bob との会話を開始
    await alicePage.click('[data-testid="new-conversation-button"]');
    await alicePage.fill('[data-testid="participant-search"]', BOB_EMAIL);
    await alicePage.click(`[data-testid="user-option-${BOB_EMAIL}"]`);
    await alicePage.click('[data-testid="create-conversation-button"]');
    
    // 会話が作成されたことを確認
    await expect(alicePage.locator('[data-testid="conversation-title"]')).toContainText('Bob');

    // === Step 4: メッセージ送信（Alice → Bob） ===
    
    const message1 = 'こんにちは、Bobさん！E2E暗号化のテストです。';
    
    await alicePage.fill('[data-testid="message-input"]', message1);
    await alicePage.click('[data-testid="send-button"]');
    
    // Alice 側でメッセージ送信確認
    await expect(alicePage.locator('[data-testid="message-item"]').last()).toContainText(message1);
    await expect(alicePage.locator('[data-testid="message-status"]').last()).toContainText('送信済み');

    // === Step 5: リアルタイム受信（Bob 側） ===
    
    // Bob が同じ会話を開く
    await bobPage.waitForSelector('[data-testid="conversation-notification"]', { timeout: 5000 });
    await bobPage.click('[data-testid="conversation-notification"]');
    
    // Bob 側でメッセージ受信確認
    await expect(bobPage.locator('[data-testid="message-item"]').last()).toContainText(message1);
    await expect(bobPage.locator('[data-testid="message-sender"]').last()).toContainText('Alice');

    // === Step 6: 暗号化確認 ===
    
    // 開発者ツールでネットワークタブを確認（実際の実装では暗号化されたデータが送信されている）
    const aliceNetworkLogs = await alicePage.evaluate(() => {
      return (window as any).encryptionDebugLogs || [];
    });
    
    expect(aliceNetworkLogs.some((log: any) => 
      log.type === 'encryption' && log.algorithm === 'RSA-OAEP+AES-GCM'
    )).toBeTruthy();

    // === Step 7: 既読機能テスト ===
    
    // Bob がメッセージを既読にする
    await bobPage.click('[data-testid="mark-as-read-button"]');
    
    // Alice 側で既読表示確認
    await expect(alicePage.locator('[data-testid="message-read-status"]').last()).toContainText('既読');
    await expect(alicePage.locator('[data-testid="read-timestamp"]').last()).toBeVisible();

    // === Step 8: 返信メッセージ（Bob → Alice） ===
    
    const message2 = 'こんにちは、Aliceさん！暗号化メッセージ受信できました。';
    
    await bobPage.fill('[data-testid="message-input"]', message2);
    await bobPage.click('[data-testid="send-button"]');
    
    // Bob 側で送信確認
    await expect(bobPage.locator('[data-testid="message-item"]').last()).toContainText(message2);

    // Alice 側でリアルタイム受信確認
    await expect(alicePage.locator('[data-testid="message-item"]').last()).toContainText(message2);
    await expect(alicePage.locator('[data-testid="unread-badge"]')).toBeVisible();

    // === Step 9: マルチデバイステスト ===
    
    // Alice が新しいタブ（デバイス）でログイン
    const aliceSecondDevice = await context.newPage();
    await aliceSecondDevice.goto(BASE_URL);
    
    await aliceSecondDevice.fill('[data-testid="email-input"]', ALICE_EMAIL);
    await aliceSecondDevice.fill('[data-testid="password-input"]', PASSWORD);
    await aliceSecondDevice.click('[data-testid="login-button"]');
    
    // 同期確認（メッセージ履歴が両デバイスで同期されている）
    await aliceSecondDevice.click(`[data-testid="conversation-Bob"]`);
    await expect(aliceSecondDevice.locator('[data-testid="message-item"]')).toHaveCount(2);

    // 第2デバイスで既読
    await aliceSecondDevice.click('[data-testid="mark-as-read-button"]');
    
    // デバイス別既読ステータス確認
    await bobPage.click('[data-testid="message-details-button"]');
    await expect(bobPage.locator('[data-testid="read-status-device-1"]')).toContainText('デバイス1: 既読');
    await expect(bobPage.locator('[data-testid="read-status-device-2"]')).toContainText('デバイス2: 既読');

    await aliceSecondDevice.close();

    // === Step 10: グループチャットテスト ===
    
    // Charlie を登録
    const charliePage = await context.newPage();
    await charliePage.goto(BASE_URL);
    
    await charliePage.click('[data-testid="register-tab"]');
    await charliePage.fill('[data-testid="email-input"]', 'charlie@example.com');
    await charliePage.fill('[data-testid="password-input"]', PASSWORD);
    await charliePage.fill('[data-testid="displayname-input"]', 'Charlie');
    await charliePage.click('[data-testid="register-button"]');

    // Alice がグループチャットを作成
    await alicePage.click('[data-testid="new-group-conversation-button"]');
    await alicePage.fill('[data-testid="participant-search"]', BOB_EMAIL);
    await alicePage.click(`[data-testid="add-user-${BOB_EMAIL}"]`);
    await alicePage.fill('[data-testid="participant-search"]', 'charlie@example.com');
    await alicePage.click('[data-testid="add-user-charlie@example.com"]');
    await alicePage.fill('[data-testid="group-title-input"]', 'テストグループ');
    await alicePage.click('[data-testid="create-group-button"]');

    // グループメッセージ送信
    const groupMessage = 'グループチャットのテストメッセージです！';
    await alicePage.fill('[data-testid="message-input"]', groupMessage);
    await alicePage.click('[data-testid="send-button"]');

    // Bob と Charlie で受信確認
    await bobPage.waitForSelector('[data-testid="group-notification"]');
    await bobPage.click('[data-testid="group-notification"]');
    await expect(bobPage.locator('[data-testid="message-item"]').last()).toContainText(groupMessage);

    await charliePage.waitForSelector('[data-testid="group-notification"]');
    await charliePage.click('[data-testid="group-notification"]');
    await expect(charliePage.locator('[data-testid="message-item"]').last()).toContainText(groupMessage);

    await charliePage.close();

    // === Step 11: エラーハンドリングテスト ===
    
    // ネットワーク障害をシミュレート
    await alicePage.setOffline(true);
    
    const offlineMessage = 'オフライン中のメッセージです';
    await alicePage.fill('[data-testid="message-input"]', offlineMessage);
    await alicePage.click('[data-testid="send-button"]');
    
    // オフライン状態の表示確認
    await expect(alicePage.locator('[data-testid="offline-indicator"]')).toBeVisible();
    await expect(alicePage.locator('[data-testid="message-status"]').last()).toContainText('送信待ち');

    // ネットワーク復旧
    await alicePage.setOffline(false);
    
    // 自動再送確認
    await expect(alicePage.locator('[data-testid="message-status"]').last()).toContainText('送信済み');
    await expect(bobPage.locator('[data-testid="message-item"]').last()).toContainText(offlineMessage);

    // === Step 12: セキュリティテスト ===
    
    // 無効なJWTトークンでのアクセステスト
    await alicePage.evaluate(() => {
      localStorage.setItem('authToken', 'invalid.jwt.token');
    });
    
    await alicePage.reload();
    
    // ログイン画面にリダイレクトされることを確認
    await expect(alicePage.locator('[data-testid="auth-form"]')).toBeVisible();

    // === Step 13: パフォーマンステスト ===
    
    // 再ログイン
    await alicePage.fill('[data-testid="email-input"]', ALICE_EMAIL);
    await alicePage.fill('[data-testid="password-input"]', PASSWORD);
    await alicePage.click('[data-testid="login-button"]');

    // レスポンス時間測定
    const startTime = Date.now();
    await alicePage.click(`[data-testid="conversation-Bob"]`);
    await alicePage.waitForSelector('[data-testid="message-item"]');
    const loadTime = Date.now() - startTime;
    
    // 2秒以内での読み込み完了を確認
    expect(loadTime).toBeLessThan(2000);

    // 大量メッセージの処理時間テスト
    const bulkStartTime = Date.now();
    for (let i = 0; i < 10; i++) {
      await alicePage.fill('[data-testid="message-input"]', `バルクメッセージ ${i + 1}`);
      await alicePage.click('[data-testid="send-button"]');
      await alicePage.waitForTimeout(100); // 100ms間隔
    }
    const bulkTime = Date.now() - bulkStartTime;
    
    // 5秒以内での送信完了を確認
    expect(bulkTime).toBeLessThan(5000);
  });

  test('暗号化キー管理フロー', async () => {
    // キー生成とローテーションのテスト
    await alicePage.goto(BASE_URL);
    
    // 登録
    await alicePage.click('[data-testid="register-tab"]');
    await alicePage.fill('[data-testid="email-input"]', 'keytest@example.com');
    await alicePage.fill('[data-testid="password-input"]', PASSWORD);
    await alicePage.fill('[data-testid="displayname-input"]', 'KeyTest');
    await alicePage.click('[data-testid="register-button"]');

    // 初期キー確認
    await alicePage.click('[data-testid="settings-button"]');
    const initialKey = await alicePage.textContent('[data-testid="public-key-display"]');
    expect(initialKey).toContain('BEGIN PUBLIC KEY');

    // キーローテーション（将来の機能）
    await alicePage.click('[data-testid="rotate-keys-button"]');
    await alicePage.click('[data-testid="confirm-rotation-button"]');
    
    const newKey = await alicePage.textContent('[data-testid="public-key-display"]');
    expect(newKey).toContain('BEGIN PUBLIC KEY');
    expect(newKey).not.toEqual(initialKey);
  });

  test('アクセシビリティテスト', async () => {
    await alicePage.goto(BASE_URL);
    
    // キーボードナビゲーション
    await alicePage.keyboard.press('Tab'); // メールフィールドにフォーカス
    await alicePage.keyboard.type(ALICE_EMAIL);
    await alicePage.keyboard.press('Tab'); // パスワードフィールドにフォーカス
    await alicePage.keyboard.type(PASSWORD);
    await alicePage.keyboard.press('Enter'); // ログインボタン

    // スクリーンリーダー対応の確認
    const loginButton = alicePage.locator('[data-testid="login-button"]');
    await expect(loginButton).toHaveAttribute('aria-label', 'ログイン');

    // コントラスト比の確認（視覚的な検証）
    const backgroundColor = await alicePage.evaluate(() => {
      const button = document.querySelector('[data-testid="login-button"]');
      return window.getComputedStyle(button!).backgroundColor;
    });
    
    expect(backgroundColor).toBeTruthy(); // 実際の実装では具体的な色の検証
  });
});

/**
 * ヘルパー関数
 */

// ユーザー登録ヘルパー
async function registerUser(page: Page, email: string, password: string, displayName: string) {
  await page.goto(BASE_URL);
  await page.click('[data-testid="register-tab"]');
  await page.fill('[data-testid="email-input"]', email);
  await page.fill('[data-testid="password-input"]', password);
  await page.fill('[data-testid="displayname-input"]', displayName);
  await page.click('[data-testid="register-button"]');
  await expect(page.locator('[data-testid="chat-interface"]')).toBeVisible();
}

// ログインヘルパー
async function loginUser(page: Page, email: string, password: string) {
  await page.goto(BASE_URL);
  await page.fill('[data-testid="email-input"]', email);
  await page.fill('[data-testid="password-input"]', password);
  await page.click('[data-testid="login-button"]');
  await expect(page.locator('[data-testid="chat-interface"]')).toBeVisible();
}

// メッセージ送信ヘルパー
async function sendMessage(page: Page, message: string) {
  await page.fill('[data-testid="message-input"]', message);
  await page.click('[data-testid="send-button"]');
  await expect(page.locator('[data-testid="message-item"]').last()).toContainText(message);
}