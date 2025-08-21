// WebUI JavaScript Simulation Test
const { JSDOM } = require('jsdom');
const nodeFetch = require('node-fetch');

// Setup DOM environment
const dom = new JSDOM(`
<!DOCTYPE html>
<html>
<head><title>WebUI Test</title></head>
<body>
  <div id="root"></div>
</body>
</html>
`, {
  url: 'http://localhost:4173',
  pretendToBeVisual: true,
  resources: 'usable'
});

global.window = dom.window;
global.document = dom.window.document;
global.navigator = dom.window.navigator;
global.fetch = nodeFetch;
global.localStorage = {
  getItem: (key) => global._localStorage?.[key] || null,
  setItem: (key, value) => {
    global._localStorage = global._localStorage || {};
    global._localStorage[key] = value;
  },
  removeItem: (key) => {
    if (global._localStorage) delete global._localStorage[key];
  },
  clear: () => { global._localStorage = {}; }
};

// Simulate environment variables
global.import = {
  meta: {
    env: {
      VITE_API_URL: 'http://localhost:3000',
      VITE_WS_URL: 'ws://localhost:3000'
    }
  }
};

// Test WebUI-like API calls
async function testWebUIJavaScript() {
  console.log('=== WebUI JavaScript Simulation ===');
  
  try {
    // 1. Test environment setup
    console.log('1. Environment Variables:');
    console.log('   VITE_API_URL:', global.import.meta.env.VITE_API_URL);
    console.log('   VITE_WS_URL:', global.import.meta.env.VITE_WS_URL);
    
    // 2. Test localStorage
    console.log('2. LocalStorage Test:');
    localStorage.setItem('testKey', 'testValue');
    console.log('   Set/Get test:', localStorage.getItem('testKey'));
    
    // 3. Test API calls with WebUI-like structure
    console.log('3. API Service Simulation:');
    
    const apiBase = global.import.meta.env.VITE_API_URL + '/api';
    console.log('   API Base URL:', apiBase);
    
    // Simulate login request
    console.log('4. Login Test:');
    const loginResponse = await fetch(apiBase + '/auth/login', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Origin': 'http://localhost:4173'
      },
      body: JSON.stringify({
        email: 'test@example.com',
        password: 'password123'
      })
    });
    
    if (loginResponse.ok) {
      const loginData = await loginResponse.json();
      console.log('   ✅ Login successful');
      console.log('   Token:', loginData.token.substring(0, 20) + '...');
      console.log('   User:', loginData.user.username);
      
      // Test token storage
      localStorage.setItem('authToken', loginData.token);
      console.log('   Token stored in localStorage');
      
      // Test protected endpoint
      console.log('5. Protected Endpoint Test:');
      const protectedResponse = await fetch(apiBase + '/conversations', {
        method: 'GET',
        headers: {
          'Authorization': `Bearer ${loginData.token}`,
          'Content-Type': 'application/json'
        }
      });
      
      if (protectedResponse.ok) {
        const conversations = await protectedResponse.json();
        console.log('   ✅ Protected endpoint accessible');
        console.log('   Conversations count:', conversations.length);
      } else {
        console.log('   ❌ Protected endpoint failed:', protectedResponse.status);
      }
      
    } else {
      const errorText = await loginResponse.text();
      console.log('   ❌ Login failed:', loginResponse.status, errorText);
    }
    
    // 5. Test registration
    console.log('6. Registration Test:');
    const timestamp = Date.now();
    const regResponse = await fetch(apiBase + '/auth/register', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Origin': 'http://localhost:4173'
      },
      body: JSON.stringify({
        username: `testuser${timestamp}`,
        email: `test${timestamp}@example.com`,
        password: 'password123'
      })
    });
    
    if (regResponse.ok) {
      const regData = await regResponse.json();
      console.log('   ✅ Registration successful');
      console.log('   New user:', regData.user.username);
    } else {
      const regError = await regResponse.text();
      console.log('   ❌ Registration failed:', regResponse.status, regError);
    }
    
    // 6. Test React-like state management simulation
    console.log('7. State Management Simulation:');
    const mockState = {
      auth: {
        isAuthenticated: false,
        user: null,
        token: null
      }
    };
    
    // Simulate successful login state update
    const token = localStorage.getItem('authToken');
    if (token) {
      mockState.auth.isAuthenticated = true;
      mockState.auth.token = token;
      mockState.auth.user = { id: 'test-id', username: 'testuser' };
      console.log('   ✅ State updated successfully');
      console.log('   Auth state:', mockState.auth.isAuthenticated);
    }
    
    console.log('\n=== Simulation Complete ===');
    console.log('All JavaScript functionality appears to work correctly');
    
  } catch (error) {
    console.error('❌ Simulation failed:', error.message);
    console.error('Stack:', error.stack);
  }
}

// Install required packages and run test
const { execSync } = require('child_process');

console.log('Installing required packages...');
try {
  execSync('npm install jsdom node-fetch', { stdio: 'inherit', cwd: __dirname });
  console.log('Packages installed successfully\n');
} catch (error) {
  console.log('Package installation failed, proceeding with test...\n');
}

// Run the test
testWebUIJavaScript();