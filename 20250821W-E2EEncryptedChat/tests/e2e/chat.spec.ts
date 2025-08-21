import { test, expect, Page } from '@playwright/test';

test.describe('E2E Encrypted Chat Application', () => {
  let alicePage: Page;
  let bobPage: Page;

  test.beforeEach(async ({ browser }) => {
    const aliceContext = await browser.newContext();
    const bobContext = await browser.newContext();
    
    alicePage = await aliceContext.newPage();
    bobPage = await bobContext.newPage();
    
    await alicePage.goto('http://localhost:3000');
    await bobPage.goto('http://localhost:3000');
  });

  test.afterEach(async () => {
    await alicePage.close();
    await bobPage.close();
  });

  test('should create encrypted chat session', async () => {
    await alicePage.fill('[data-testid="email-input"]', 'alice@example.com');
    await alicePage.fill('[data-testid="password-input"]', 'AliceSecurePass123!');
    await alicePage.click('[data-testid="signup-button"]');

    await bobPage.fill('[data-testid="email-input"]', 'bob@example.com');
    await bobPage.fill('[data-testid="password-input"]', 'BobSecurePass123!');
    await bobPage.click('[data-testid="signup-button"]');

    await expect(alicePage.locator('[data-testid="encryption-indicator"]')).toContainText('End-to-End Encrypted');
    await expect(bobPage.locator('[data-testid="encryption-indicator"]')).toContainText('End-to-End Encrypted');
  });

  test('should exchange encrypted messages', async () => {
    await alicePage.click('[data-testid="new-chat-button"]');
    await alicePage.fill('[data-testid="search-user"]', 'bob@example.com');
    await alicePage.click('[data-testid="start-chat-button"]');

    const aliceMessage = 'Hello Bob, this is a secure message!';
    await alicePage.fill('[data-testid="message-input"]', aliceMessage);
    await alicePage.press('[data-testid="message-input"]', 'Enter');

    await expect(bobPage.locator('[data-testid="message-content"]').first()).toContainText(aliceMessage);

    const bobMessage = 'Hi Alice, message received securely!';
    await bobPage.fill('[data-testid="message-input"]', bobMessage);
    await bobPage.press('[data-testid="message-input"]', 'Enter');

    await expect(alicePage.locator('[data-testid="message-content"]').last()).toContainText(bobMessage);
  });

  test('should verify security numbers', async () => {
    await alicePage.click('[data-testid="verify-button"]');
    const aliceSecurityNumber = await alicePage.locator('[data-testid="security-number"]').textContent();

    await bobPage.click('[data-testid="verify-button"]');
    const bobSecurityNumber = await bobPage.locator('[data-testid="security-number"]').textContent();

    await alicePage.fill('[data-testid="verify-input"]', bobSecurityNumber || '');
    await alicePage.click('[data-testid="confirm-verify-button"]');

    await expect(alicePage.locator('[data-testid="verification-status"]')).toContainText('Verified');
    await expect(bobPage.locator('[data-testid="verification-status"]')).toContainText('Verified');
  });

  test('should handle key rotation', async () => {
    await alicePage.click('[data-testid="settings-button"]');
    await alicePage.click('[data-testid="rotate-keys-button"]');

    await expect(alicePage.locator('[data-testid="key-rotation-status"]')).toContainText('Keys rotated successfully');

    const messageAfterRotation = 'Message after key rotation';
    await alicePage.fill('[data-testid="message-input"]', messageAfterRotation);
    await alicePage.press('[data-testid="message-input"]', 'Enter');

    await expect(bobPage.locator('[data-testid="message-content"]').last()).toContainText(messageAfterRotation);
  });

  test('should show encryption indicators', async () => {
    const encryptionBadge = alicePage.locator('[data-testid="encryption-badge"]');
    await expect(encryptionBadge).toBeVisible();
    await expect(encryptionBadge).toHaveAttribute('title', 'Messages are end-to-end encrypted');

    const encryptionIndicator = alicePage.locator('[data-testid="encryption-indicator"]');
    await expect(encryptionIndicator).toBeVisible();
    await expect(encryptionIndicator).toContainText('End-to-End Encrypted');
  });

  test('should handle message deletion', async () => {
    const message = 'This message will be deleted';
    await alicePage.fill('[data-testid="message-input"]', message);
    await alicePage.press('[data-testid="message-input"]', 'Enter');

    const messageElement = alicePage.locator('[data-testid="message-content"]').filter({ hasText: message });
    await messageElement.click({ button: 'right' });
    await alicePage.click('[data-testid="delete-message-button"]');

    await expect(messageElement).not.toBeVisible();
    await expect(bobPage.locator('[data-testid="message-content"]').filter({ hasText: message })).toContainText('This message was deleted');
  });

  test('should handle offline message queue', async () => {
    await alicePage.evaluate(() => window.navigator.onLine = false);

    const offlineMessage = 'Message sent while offline';
    await alicePage.fill('[data-testid="message-input"]', offlineMessage);
    await alicePage.press('[data-testid="message-input"]', 'Enter');

    await expect(alicePage.locator('[data-testid="message-status"]').last()).toContainText('Pending');

    await alicePage.evaluate(() => window.navigator.onLine = true);
    await alicePage.waitForTimeout(1000);

    await expect(alicePage.locator('[data-testid="message-status"]').last()).toContainText('Sent');
    await expect(bobPage.locator('[data-testid="message-content"]').last()).toContainText(offlineMessage);
  });

  test('should export and import chat history', async () => {
    const messages = ['Message 1', 'Message 2', 'Message 3'];
    
    for (const msg of messages) {
      await alicePage.fill('[data-testid="message-input"]', msg);
      await alicePage.press('[data-testid="message-input"]', 'Enter');
      await alicePage.waitForTimeout(500);
    }

    await alicePage.click('[data-testid="settings-button"]');
    await alicePage.click('[data-testid="export-chat-button"]');

    const download = await alicePage.waitForEvent('download');
    expect(download.suggestedFilename()).toContain('encrypted-chat-export');

    await alicePage.click('[data-testid="clear-chat-button"]');
    await expect(alicePage.locator('[data-testid="message-content"]')).toHaveCount(0);

    const importInput = alicePage.locator('[data-testid="import-input"]');
    await importInput.setInputFiles(await download.path());

    for (const msg of messages) {
      await expect(alicePage.locator('[data-testid="message-content"]').filter({ hasText: msg })).toBeVisible();
    }
  });
});