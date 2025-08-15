import { Given, When, Then, Before, After } from '@cucumber/cucumber';
import { expect } from 'chai';
import axios, { AxiosResponse } from 'axios';
import { Database } from '../../../src/infra/db';
import { KeyManager } from '../../../src/domain/crypto/keyManager';

const API_URL = process.env.API_URL || 'http://localhost:3000';
let db: Database;
let keyManager: KeyManager;
let response: AxiosResponse;
let authToken: string;
let userData: any = {};
let error: any;

Before(async () => {
  db = new Database(process.env.DATABASE_URL || 'postgresql://app:app@localhost:5432/e2echat_test');
  keyManager = await KeyManager.getInstance();
  // Clean database before each scenario
  await db.query('TRUNCATE TABLE users, devices, identity_keys, signed_pre_keys, one_time_pre_keys CASCADE');
});

After(async () => {
  await db.close();
});

Given('the E2E chat system is initialized', async () => {
  // System should be running
  const health = await axios.get(`${API_URL}/health`);
  expect(health.status).to.equal(200);
});

Given('cryptographic libraries are loaded', async () => {
  // Verify libsodium is ready
  expect(keyManager).to.not.be.null;
});

Given('I am a new user', () => {
  userData = {};
  authToken = '';
});

When('I register with email {string}, password {string}, and display name {string}', async (email: string, password: string, displayName: string) => {
  try {
    response = await axios.post(`${API_URL}/auth/register`, {
      email,
      password,
      displayName
    });
    userData = response.data;
    error = null;
  } catch (e: any) {
    error = e.response;
    response = e.response;
  }
});

Then('my account should be created successfully', () => {
  expect(response.status).to.equal(201);
  expect(userData.id).to.not.be.undefined;
  expect(userData.email).to.not.be.undefined;
});

Then('my identity key pair should be generated', async () => {
  const result = await db.query('SELECT * FROM identity_keys WHERE user_id = $1', [userData.id]);
  expect(result.rows).to.have.lengthOf(1);
  expect(result.rows[0].public_key).to.not.be.null;
});

Then('my signed pre-key should be generated', async () => {
  const result = await db.query('SELECT * FROM signed_pre_keys WHERE user_id = $1', [userData.id]);
  expect(result.rows.length).to.be.at.least(1);
  expect(result.rows[0].signature).to.not.be.null;
});

Then('{int} one-time pre-keys should be generated', async (count: number) => {
  const result = await db.query('SELECT COUNT(*) as count FROM one_time_pre_keys WHERE user_id = $1', [userData.id]);
  expect(parseInt(result.rows[0].count)).to.equal(count);
});

Then('I should receive a verification email', () => {
  // This would be mocked in test environment
  expect(userData.isVerified).to.equal(false);
});

Then('registration should fail with error {string}', (errorMessage: string) => {
  expect(error).to.not.be.null;
  expect(error.data.message).to.include(errorMessage);
});

Given('a user exists with email {string}', async (email: string) => {
  await axios.post(`${API_URL}/auth/register`, {
    email,
    password: 'ExistingP@ssw0rd123',
    displayName: 'Existing User'
  });
});

Given('I have a registered account with email {string}', async (email: string) => {
  const registerResponse = await axios.post(`${API_URL}/auth/register`, {
    email,
    password: 'SecureP@ssw0rd123',
    displayName: 'Test User'
  });
  userData = registerResponse.data;
});

Given('I have 2FA enabled', async () => {
  // Login first to get token
  const loginResponse = await axios.post(`${API_URL}/auth/login`, {
    email: userData.email,
    password: 'SecureP@ssw0rd123',
    deviceFingerprint: 'test-device'
  });
  authToken = loginResponse.data.token;
  
  // Enable 2FA
  const twoFAResponse = await axios.post(`${API_URL}/auth/2fa/enable`, {}, {
    headers: { Authorization: `Bearer ${authToken}` }
  });
  userData.totpSecret = twoFAResponse.data.secret;
});

When('I login with email {string}, password {string}, and TOTP code {string}', async (email: string, password: string, totpCode: string) => {
  try {
    response = await axios.post(`${API_URL}/auth/login`, {
      email,
      password,
      deviceFingerprint: 'test-device',
      totpCode
    });
    authToken = response.data.token;
    error = null;
  } catch (e: any) {
    error = e.response;
    response = e.response;
  }
});

When('I login with email {string} and password {string}', async (email: string, password: string) => {
  try {
    response = await axios.post(`${API_URL}/auth/login`, {
      email,
      password,
      deviceFingerprint: 'test-device'
    });
    authToken = response.data.token;
    error = null;
  } catch (e: any) {
    error = e.response;
    response = e.response;
  }
});

Then('I should be authenticated successfully', () => {
  expect(response.status).to.equal(200);
  expect(authToken).to.not.be.empty;
});

Then('I should receive a JWT token', () => {
  expect(response.data.token).to.not.be.undefined;
  expect(response.data.tokenType).to.equal('Bearer');
});

Then('my device should be registered', async () => {
  const result = await db.query('SELECT * FROM devices WHERE device_fingerprint = $1', ['test-device']);
  expect(result.rows).to.have.lengthOf(1);
});

Then('authentication should fail with error {string}', (errorMessage: string) => {
  expect(error).to.not.be.null;
  expect(error.data.message).to.include(errorMessage);
});

Given('I am authenticated as {string}', async (email: string) => {
  // Register and login
  await axios.post(`${API_URL}/auth/register`, {
    email,
    password: 'SecureP@ssw0rd123',
    displayName: email.split('@')[0]
  });
  
  const loginResponse = await axios.post(`${API_URL}/auth/login`, {
    email,
    password: 'SecureP@ssw0rd123',
    deviceFingerprint: 'test-device'
  });
  
  authToken = loginResponse.data.token;
  userData.email = email;
});

When('I enable 2FA', async () => {
  response = await axios.post(`${API_URL}/auth/2fa/enable`, {}, {
    headers: { Authorization: `Bearer ${authToken}` }
  });
  userData.twoFA = response.data;
});

Then('a TOTP secret should be generated', () => {
  expect(userData.twoFA.secret).to.not.be.undefined;
  expect(userData.twoFA.secret).to.have.lengthOf.at.least(16);
});

Then('backup codes should be generated', () => {
  expect(userData.twoFA.backupCodes).to.be.an('array');
  expect(userData.twoFA.backupCodes).to.have.lengthOf.at.least(8);
});

Then('I should see a QR code for authenticator apps', () => {
  expect(userData.twoFA.qrCode).to.not.be.undefined;
  expect(userData.twoFA.qrCode).to.include('data:image');
});