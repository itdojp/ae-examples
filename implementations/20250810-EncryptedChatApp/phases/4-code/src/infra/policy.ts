import { loadPolicy } from '@open-policy-agent/opa-wasm';
import fs from 'fs';
import path from 'path';

export interface PolicyInput {
  user?: {
    id: string;
    email: string;
    roles?: string[];
  };
  action?: string;
  resource?: {
    type: string;
    id?: string;
    userId?: string;
    senderId?: string;
    recipientId?: string;
    timestamp?: number;
    used?: boolean;
  };
  path: string;
  method: string;
  body?: any;
  token?: {
    exp: number;
    iat: number;
  };
  request_count?: number;
  password?: string;
}

export interface PolicyResult {
  allow: boolean;
  audit_required?: boolean;
  rate_limit_exceeded?: boolean;
  message_access_allowed?: boolean;
  key_modification_allowed?: boolean;
  device_access_allowed?: boolean;
  password_policy_met?: boolean;
  device_fingerprint_required?: boolean;
  message_should_be_deleted?: boolean;
  one_time_key_should_be_deleted?: boolean;
  gdpr_data_access_allowed?: boolean;
  gdpr_deletion_allowed?: boolean;
  token_valid?: boolean;
}

export class PolicyEngine {
  private static instance: PolicyEngine;
  private policy: any;
  private data: any;

  private constructor() {
    this.data = {};
  }

  public static async getInstance(): Promise<PolicyEngine> {
    if (!PolicyEngine.instance) {
      PolicyEngine.instance = new PolicyEngine();
      await PolicyEngine.instance.initialize();
    }
    return PolicyEngine.instance;
  }

  private async initialize(): Promise<void> {
    try {
      // Load policy file
      const policyPath = path.join(__dirname, '../../policies/e2e-chat.rego');
      const policyContent = fs.readFileSync(policyPath, 'utf8');
      
      // Load data file
      const dataPath = path.join(__dirname, '../../policies/data.json');
      if (fs.existsSync(dataPath)) {
        const dataContent = fs.readFileSync(dataPath, 'utf8');
        this.data = JSON.parse(dataContent);
      }

      // In production, we would compile the Rego to WASM
      // For now, we'll use a simple evaluation
      this.policy = policyContent;
    } catch (error) {
      console.error('Failed to initialize policy engine:', error);
      throw error;
    }
  }

  public async evaluate(input: PolicyInput): Promise<PolicyResult> {
    // In production, this would use OPA WASM evaluation
    // For now, we'll implement basic logic based on the policy

    const result: PolicyResult = {
      allow: false,
    };

    // Check unauthenticated endpoints
    if (input.path === '/health' && input.method === 'GET') {
      result.allow = true;
      return result;
    }

    if (input.path === '/docs' && input.method === 'GET') {
      result.allow = true;
      return result;
    }

    if (input.path === '/auth/register' && input.method === 'POST' && !input.user) {
      result.allow = true;
      result.audit_required = true;
      
      // Check password policy
      if (input.password) {
        result.password_policy_met = this.checkPasswordPolicy(input.password);
      }
      return result;
    }

    if (input.path === '/auth/login' && input.method === 'POST' && !input.user) {
      result.allow = true;
      result.audit_required = true;
      
      // Check device fingerprint
      if (!input.body?.deviceFingerprint) {
        result.device_fingerprint_required = true;
        result.allow = false;
      }
      return result;
    }

    // All other endpoints require authentication
    if (!input.user?.id) {
      result.allow = false;
      return result;
    }

    // Check authenticated endpoints
    if (input.user.id) {
      // User profile access
      if (input.path === `/users/${input.user.id}` && input.method === 'GET') {
        result.allow = true;
        return result;
      }

      // 2FA endpoints
      if (input.path === '/auth/2fa/enable' && input.method === 'POST') {
        result.allow = true;
        result.audit_required = true;
        return result;
      }

      if (input.path === '/auth/2fa/verify' && input.method === 'POST') {
        result.allow = true;
        return result;
      }

      // Key management
      if (input.path === '/keys/upload' && input.method === 'POST') {
        result.allow = true;
        return result;
      }

      if (input.path.includes('/keys/bundle') && input.method === 'GET') {
        result.allow = true;
        return result;
      }

      if (input.path === '/keys/rotate/signed' && input.method === 'POST') {
        result.allow = true;
        result.audit_required = true;
        return result;
      }

      // Messaging
      if (input.path === '/messages/send' && input.method === 'POST') {
        result.allow = true;
        result.audit_required = true;
        
        // Check rate limit
        const rateLimit = { requests: 100, window: '1m' };
        if (input.request_count && input.request_count > rateLimit.requests) {
          result.rate_limit_exceeded = true;
          result.allow = false;
        }
        return result;
      }

      if (input.path.includes('/messages') && input.method === 'GET') {
        result.allow = true;
        
        // Check message access
        if (input.resource?.type === 'message') {
          result.message_access_allowed = 
            input.user.id === input.resource.senderId || 
            input.user.id === input.resource.recipientId;
        }
        return result;
      }

      // Sessions
      if (input.path.includes('/sessions') && (input.method === 'POST' || input.method === 'GET')) {
        result.allow = true;
        if (input.method === 'POST') {
          result.audit_required = true;
        }
        return result;
      }

      // Verification
      if (input.path.includes('/verification')) {
        result.allow = true;
        if (input.path.includes('/verify') && input.method === 'POST') {
          result.audit_required = true;
        }
        return result;
      }

      // WebSocket
      if (input.path === '/ws' && input.method === 'UPGRADE') {
        result.allow = true;
        return result;
      }
    }

    // Check resource-specific policies
    if (input.resource) {
      // Message retention
      if (input.resource.type === 'message' && input.resource.timestamp) {
        const messageAgeDays = (Date.now() - input.resource.timestamp) / (1000 * 60 * 60 * 24);
        result.message_should_be_deleted = messageAgeDays > 90;
      }

      // One-time key deletion
      if (input.resource.type === 'one_time_key' && input.resource.used) {
        result.one_time_key_should_be_deleted = true;
      }

      // Key modification
      if (input.resource.type === 'key' && input.user) {
        result.key_modification_allowed = input.resource.userId === input.user.id;
      }

      // Device access
      if (input.resource.type === 'device' && input.user) {
        result.device_access_allowed = input.resource.userId === input.user.id;
      }
    }

    // GDPR compliance
    if (input.action === 'data.export' && input.user && input.resource?.userId === input.user.id) {
      result.gdpr_data_access_allowed = true;
    }

    if (input.action === 'account.delete' && input.user && input.resource?.userId === input.user.id) {
      result.gdpr_deletion_allowed = true;
    }

    // Token validation
    if (input.token) {
      result.token_valid = input.token.exp > Date.now() / 1000;
    }

    return result;
  }

  private checkPasswordPolicy(password: string): boolean {
    if (password.length < 12) return false;
    if (!/[A-Z]/.test(password)) return false;
    if (!/[a-z]/.test(password)) return false;
    if (!/[0-9]/.test(password)) return false;
    if (!/[!@#$%^&*(),.?":{}|<>]/.test(password)) return false;
    return true;
  }

  public async updateData(key: string, value: any): Promise<void> {
    this.data[key] = value;
    
    // Persist data
    const dataPath = path.join(__dirname, '../../policies/data.json');
    fs.writeFileSync(dataPath, JSON.stringify(this.data, null, 2));
  }

  public async addVerification(userId: string, peerId: string, verified: boolean): Promise<void> {
    if (!this.data.verifications) {
      this.data.verifications = {};
    }
    if (!this.data.verifications[userId]) {
      this.data.verifications[userId] = {};
    }
    this.data.verifications[userId][peerId] = { verified, timestamp: Date.now() };
    await this.updateData('verifications', this.data.verifications);
  }

  public async addSession(userId1: string, userId2: string): Promise<void> {
    if (!this.data.sessions) {
      this.data.sessions = {};
    }
    if (!this.data.sessions[userId1]) {
      this.data.sessions[userId1] = {};
    }
    this.data.sessions[userId1][userId2] = { established: true, timestamp: Date.now() };
    await this.updateData('sessions', this.data.sessions);
  }

  public async incrementRateLimit(path: string, userId: string): Promise<number> {
    if (!this.data.rate_limits) {
      this.data.rate_limits = {};
    }
    
    const key = `${path}:${userId}`;
    const now = Date.now();
    
    if (!this.data.rate_limits[key]) {
      this.data.rate_limits[key] = { count: 0, window_start: now };
    }
    
    // Reset window if expired (using 1 hour as default)
    const windowDuration = 60 * 60 * 1000; // 1 hour in milliseconds
    if (now - this.data.rate_limits[key].window_start > windowDuration) {
      this.data.rate_limits[key] = { count: 1, window_start: now };
    } else {
      this.data.rate_limits[key].count++;
    }
    
    await this.updateData('rate_limits', this.data.rate_limits);
    return this.data.rate_limits[key].count;
  }
}