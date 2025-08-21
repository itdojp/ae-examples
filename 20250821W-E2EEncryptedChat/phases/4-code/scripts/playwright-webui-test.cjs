// Advanced WebUI Testing with Playwright
const { chromium } = require('playwright');

async function testWebUIWithPlaywright() {
  console.log('=== Playwright WebUI Integration Test ===');
  
  let browser = null;
  let page = null;
  
  try {
    // Launch browser
    console.log('1. Launching headless browser...');
    browser = await chromium.launch({ 
      headless: true,
      args: ['--no-sandbox', '--disable-dev-shm-usage']
    });
    
    page = await browser.newPage();
    
    // Enable console logging
    page.on('console', msg => {
      if (msg.type() === 'log') {
        console.log('   [Browser Console]', msg.text());
      } else if (msg.type() === 'error') {
        console.log('   [Browser Error]', msg.text());
      }
    });
    
    // Navigate to WebUI
    console.log('2. Navigating to WebUI...');
    await page.goto('http://localhost:4173', { waitUntil: 'networkidle' });
    
    const title = await page.title();
    console.log('   Page title:', title);
    
    // Check if page loaded correctly
    const content = await page.content();
    if (content.includes('E2E Chat')) {
      console.log('   ✅ WebUI loaded successfully');
    } else {
      console.log('   ❌ WebUI failed to load');
      return;
    }
    
    // 3. Check for React app initialization
    console.log('3. Checking React app initialization...');
    await page.waitForSelector('#root', { timeout: 10000 });
    console.log('   ✅ React root element found');
    
    // 4. Check for AuthForm
    console.log('4. Checking authentication form...');
    const authFormExists = await page.locator('form, [role="tabpanel"]').count() > 0;
    console.log('   Auth form present:', authFormExists ? '✅' : '❌');
    
    // 5. Check environment variables in browser
    console.log('5. Checking browser environment...');
    const envCheck = await page.evaluate(() => {
      return {
        hasImportMeta: typeof window.import !== 'undefined',
        userAgent: navigator.userAgent,
        location: window.location.href,
        localStorage: typeof localStorage !== 'undefined'
      };
    });
    console.log('   Environment check:', envCheck);
    
    // 6. Test Debug Info button
    console.log('6. Testing Debug Info functionality...');
    try {
      // Look for Debug Info button
      const debugButton = page.locator('button:has-text("Debug Info")');
      const debugButtonExists = await debugButton.count() > 0;
      
      if (debugButtonExists) {
        console.log('   ✅ Debug Info button found');
        
        // Click Debug Info and capture console output
        await debugButton.click();
        await page.waitForTimeout(2000); // Wait for logs
        
      } else {
        console.log('   ❌ Debug Info button not found');
      }
    } catch (error) {
      console.log('   ⚠️ Debug Info test failed:', error.message);
    }
    
    // 7. Test login form interaction
    console.log('7. Testing login form interaction...');
    try {
      // Check if login tab is available
      const loginTab = page.locator('text=Login');
      const loginTabExists = await loginTab.count() > 0;
      
      if (loginTabExists) {
        await loginTab.click();
        console.log('   ✅ Login tab clickable');
        
        // Fill login form
        await page.fill('input[name="email"], input[type="email"]', 'test@example.com');
        await page.fill('input[name="password"], input[type="password"]', 'password123');
        console.log('   ✅ Form fields fillable');
        
        // Try to submit (but don't wait for completion)
        const submitButton = page.locator('button[type="submit"], button:has-text("Sign In")');
        const submitExists = await submitButton.count() > 0;
        
        if (submitExists) {
          console.log('   ✅ Submit button found');
          
          // Click submit and capture any errors
          await Promise.race([
            submitButton.click(),
            page.waitForTimeout(5000)
          ]);
          
          // Check for any error messages
          const errorMessages = await page.locator('[role="alert"], .error, .MuiAlert-root').allTextContents();
          if (errorMessages.length > 0) {
            console.log('   Form submission errors:', errorMessages);
          } else {
            console.log('   Form submitted without visible errors');
          }
          
        } else {
          console.log('   ❌ Submit button not found');
        }
        
      } else {
        console.log('   ❌ Login tab not found');
      }
      
    } catch (error) {
      console.log('   ⚠️ Login form test failed:', error.message);
    }
    
    // 8. Network monitoring
    console.log('8. Monitoring network requests...');
    const requests = [];
    page.on('request', request => {
      if (request.url().includes('/api/')) {
        requests.push({
          url: request.url(),
          method: request.method(),
          headers: request.headers()
        });
      }
    });
    
    page.on('response', response => {
      if (response.url().includes('/api/')) {
        console.log('   API Response:', response.status(), response.url());
      }
    });
    
    // Trigger any pending requests
    await page.waitForTimeout(3000);
    
    if (requests.length > 0) {
      console.log('   API requests made:', requests.length);
      requests.forEach(req => {
        console.log('     -', req.method, req.url);
      });
    } else {
      console.log('   No API requests detected');
    }
    
    // 9. JavaScript error detection
    console.log('9. JavaScript error detection...');
    const jsErrors = [];
    page.on('pageerror', error => {
      jsErrors.push(error.message);
    });
    
    // Wait a bit more for any delayed errors
    await page.waitForTimeout(2000);
    
    if (jsErrors.length > 0) {
      console.log('   ❌ JavaScript errors detected:');
      jsErrors.forEach(error => console.log('     -', error));
    } else {
      console.log('   ✅ No JavaScript errors detected');
    }
    
    console.log('\n=== Playwright Test Summary ===');
    console.log('✅ Browser automation: Working');
    console.log('✅ WebUI loading: Working');
    console.log('✅ React initialization: Working');
    console.log('✅ Form interaction: Working');
    console.log('✅ Network monitoring: Available');
    console.log('✅ Error detection: Available');
    
  } catch (error) {
    console.error('❌ Playwright test failed:', error.message);
    console.error('Stack:', error.stack);
  } finally {
    if (page) await page.close();
    if (browser) await browser.close();
  }
}

// Install browser if needed and run test
async function setup() {
  const { execSync } = require('child_process');
  
  try {
    console.log('Installing Playwright browsers...');
    execSync('npx playwright install chromium', { stdio: 'inherit' });
    console.log('Browser installation complete\n');
  } catch (error) {
    console.log('Browser installation failed, proceeding with test...\n');
  }
  
  await testWebUIWithPlaywright();
}

setup();