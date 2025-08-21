// Frontend API Test using Node.js with fetch-like behavior
const https = require('https');
const http = require('http');

// Simulate fetch API
function fetch(url, options = {}) {
    return new Promise((resolve, reject) => {
        const urlObj = new URL(url);
        const lib = urlObj.protocol === 'https:' ? https : http;
        
        const reqOptions = {
            hostname: urlObj.hostname,
            port: urlObj.port || (urlObj.protocol === 'https:' ? 443 : 80),
            path: urlObj.pathname + urlObj.search,
            method: options.method || 'GET',
            headers: options.headers || {}
        };
        
        const req = lib.request(reqOptions, (res) => {
            let data = '';
            res.on('data', chunk => data += chunk);
            res.on('end', () => {
                resolve({
                    ok: res.statusCode >= 200 && res.statusCode < 300,
                    status: res.statusCode,
                    statusText: res.statusMessage,
                    headers: res.headers,
                    json: () => Promise.resolve(JSON.parse(data)),
                    text: () => Promise.resolve(data)
                });
            });
        });
        
        req.on('error', reject);
        
        if (options.body) {
            req.write(options.body);
        }
        
        req.end();
    });
}

async function testFrontendAPI() {
    console.log('=== Frontend API Simulation Test ===');
    
    try {
        // Test 1: Health check
        console.log('1. Testing health endpoint...');
        const healthResponse = await fetch('http://localhost:3000/health');
        const healthData = await healthResponse.json();
        console.log('✅ Health check:', healthData);
        
        // Test 2: Login test
        console.log('2. Testing login with exact frontend headers...');
        const loginResponse = await fetch('http://localhost:3000/api/auth/login', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
                'Origin': 'http://localhost:4173',
                'Referer': 'http://localhost:4173/',
                'User-Agent': 'Mozilla/5.0 (Frontend Test)'
            },
            body: JSON.stringify({
                email: 'test@example.com',
                password: 'password123'
            })
        });
        
        if (loginResponse.ok) {
            const loginData = await loginResponse.json();
            console.log('✅ Login successful:', loginData);
            
            // Test 3: Token validation
            const token = loginData.token;
            console.log('3. Testing protected endpoint with token...');
            const protectedResponse = await fetch('http://localhost:3000/api/conversations', {
                method: 'GET',
                headers: {
                    'Authorization': `Bearer ${token}`,
                    'Content-Type': 'application/json',
                    'Origin': 'http://localhost:4173'
                }
            });
            
            if (protectedResponse.ok) {
                const conversations = await protectedResponse.json();
                console.log('✅ Protected endpoint access successful:', conversations);
            } else {
                console.log('❌ Protected endpoint failed:', protectedResponse.status);
            }
            
        } else {
            const errorText = await loginResponse.text();
            console.log('❌ Login failed:', loginResponse.status, errorText);
        }
        
        // Test 4: Registration test
        console.log('4. Testing registration...');
        const timestamp = Date.now();
        const regResponse = await fetch('http://localhost:3000/api/auth/register', {
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
            console.log('✅ Registration successful:', regData);
        } else {
            const regError = await regResponse.text();
            console.log('❌ Registration failed:', regResponse.status, regError);
        }
        
    } catch (error) {
        console.error('❌ Test failed with error:', error.message);
    }
}

// Run the test
testFrontendAPI();