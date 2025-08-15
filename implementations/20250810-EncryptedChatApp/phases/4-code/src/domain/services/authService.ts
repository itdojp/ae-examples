import { v4 as uuidv4 } from 'uuid';
import jwt from 'jsonwebtoken';
import speakeasy from 'speakeasy';
import QRCode from 'qrcode';
import bcrypt from 'bcrypt';
import { 
  User, 
  Device,
  AuthToken,
  TwoFactorAuth,
  AuthenticationError
} from '../entities';
import { UserRepository } from '../../infra/repositories/userRepository';
import { KeyService } from './keyService';
import { Database } from '../../infra/db';

export interface AuthService {
  register(email: string, password: string, displayName: string): Promise<User>;
  login(email: string, password: string, deviceFingerprint: string, totpCode?: string): Promise<AuthToken>;
  logout(token: string): Promise<void>;
  verifyToken(token: string): Promise<User | null>;
  enable2FA(userId: string): Promise<TwoFactorAuth>;
  verify2FA(userId: string, code: string): Promise<boolean>;
  refreshToken(refreshToken: string): Promise<AuthToken>;
}

export class AuthServiceImpl implements AuthService {
  private userRepository: UserRepository;
  private keyService: KeyService;
  private jwtSecret: string;
  private jwtRefreshSecret: string;
  
  constructor(
    private db: Database,
    userRepository: UserRepository,
    keyService: KeyService
  ) {
    this.userRepository = userRepository;
    this.keyService = keyService;
    this.jwtSecret = process.env.JWT_SECRET || 'development-secret-change-in-production';
    this.jwtRefreshSecret = process.env.JWT_REFRESH_SECRET || 'development-refresh-secret';
  }

  async register(email: string, password: string, displayName: string): Promise<User> {
    // Check if user already exists
    const existingUser = await this.userRepository.findByEmail(email);
    if (existingUser) {
      throw new AuthenticationError('Email already registered');
    }

    // Hash password
    const passwordHash = await bcrypt.hash(password, 12);
    
    // Create user
    const userId = uuidv4();
    
    // Save user to database with transaction
    const user = await this.db.transaction(async (client) => {
      // Save user
      const query = `
        INSERT INTO users (id, email, password_hash, display_name, is_verified, created_at, updated_at)
        VALUES ($1, $2, $3, $4, $5, NOW(), NOW())
        RETURNING *
      `;
      
      const result = await client.query(query, [
        userId,
        email,
        passwordHash,
        displayName,
        false
      ]);
      
      const newUser = this.mapToUser(result.rows[0]);
      
      // Generate and save user keys
      await this.keyService.generateUserKeys(userId);
      
      return newUser;
    });
    
    // TODO: Send verification email
    
    return user;
  }

  async login(email: string, password: string, deviceFingerprint: string, totpCode?: string): Promise<AuthToken> {
    // Get user from database
    const query = 'SELECT * FROM users WHERE email = $1';
    const result = await this.db.query(query, [email]);
    
    if (result.rows.length === 0) {
      throw new AuthenticationError('Invalid credentials');
    }
    
    const user = result.rows[0];
    
    // Verify password
    const isValidPassword = await bcrypt.compare(password, user.password_hash);
    if (!isValidPassword) {
      throw new AuthenticationError('Invalid credentials');
    }
    
    // Check 2FA if enabled
    const twoFAQuery = 'SELECT * FROM two_factor_auth WHERE user_id = $1 AND enabled = true';
    const twoFAResult = await this.db.query(twoFAQuery, [user.id]);
    
    if (twoFAResult.rows.length > 0) {
      if (!totpCode) {
        throw new AuthenticationError('2FA code required');
      }
      
      const isValid2FA = await this.verify2FA(user.id, totpCode);
      if (!isValid2FA) {
        throw new AuthenticationError('Invalid 2FA code');
      }
    }
    
    // Register or get device
    const deviceId = await this.registerDevice(user.id, deviceFingerprint);
    
    // Generate JWT tokens
    const token = jwt.sign(
      { userId: user.id, deviceId, email: user.email },
      this.jwtSecret,
      { expiresIn: '1h' }
    );
    
    const refreshToken = jwt.sign(
      { userId: user.id, deviceId },
      this.jwtRefreshSecret,
      { expiresIn: '30d' }
    );
    
    // Save token to database
    const tokenId = uuidv4();
    const expiresAt = new Date(Date.now() + 3600000); // 1 hour
    
    const tokenQuery = `
      INSERT INTO auth_tokens (id, user_id, device_id, token_hash, refresh_token_hash, expires_at, created_at)
      VALUES ($1, $2, $3, $4, $5, $6, NOW())
    `;
    
    await this.db.query(tokenQuery, [
      tokenId,
      user.id,
      deviceId,
      this.hashToken(token),
      this.hashToken(refreshToken),
      expiresAt
    ]);
    
    // Update last seen
    await this.userRepository.updateLastSeen(user.id);
    
    return {
      id: tokenId,
      userId: user.id,
      deviceId,
      token,
      refreshToken,
      expiresAt,
      createdAt: new Date()
    };
  }

  async logout(token: string): Promise<void> {
    const tokenHash = this.hashToken(token);
    
    // Delete token from database
    const query = 'DELETE FROM auth_tokens WHERE token_hash = $1';
    await this.db.query(query, [tokenHash]);
  }

  async verifyToken(token: string): Promise<User | null> {
    try {
      const decoded = jwt.verify(token, this.jwtSecret) as any;
      
      // Check if token exists in database
      const tokenHash = this.hashToken(token);
      const tokenQuery = 'SELECT * FROM auth_tokens WHERE token_hash = $1 AND expires_at > NOW()';
      const tokenResult = await this.db.query(tokenQuery, [tokenHash]);
      
      if (tokenResult.rows.length === 0) {
        return null;
      }
      
      // Get user
      return await this.userRepository.findById(decoded.userId);
    } catch (error) {
      return null;
    }
  }

  async enable2FA(userId: string): Promise<TwoFactorAuth> {
    // Generate secret
    const secret = speakeasy.generateSecret({
      name: `E2E Chat (${userId})`,
      length: 32
    });
    
    // Generate backup codes
    const backupCodes = Array.from({ length: 10 }, () => 
      Math.random().toString(36).substr(2, 8).toUpperCase()
    );
    
    // Hash backup codes
    const hashedBackupCodes = await Promise.all(
      backupCodes.map(code => bcrypt.hash(code, 10))
    );
    
    // Save to database
    const query = `
      INSERT INTO two_factor_auth (user_id, secret, backup_codes, enabled, created_at, updated_at)
      VALUES ($1, $2, $3, false, NOW(), NOW())
      ON CONFLICT (user_id) DO UPDATE
      SET secret = $2, backup_codes = $3, updated_at = NOW()
    `;
    
    await this.db.query(query, [
      userId,
      secret.base32,
      hashedBackupCodes
    ]);
    
    return {
      userId,
      secret: secret.base32,
      backupCodes,
      enabled: false,
      createdAt: new Date(),
      updatedAt: new Date()
    };
  }

  async verify2FA(userId: string, code: string): Promise<boolean> {
    // Get 2FA settings
    const query = 'SELECT * FROM two_factor_auth WHERE user_id = $1';
    const result = await this.db.query(query, [userId]);
    
    if (result.rows.length === 0) {
      return false;
    }
    
    const twoFA = result.rows[0];
    
    // Verify TOTP code
    const isValid = speakeasy.totp.verify({
      secret: twoFA.secret,
      encoding: 'base32',
      token: code,
      window: 2
    });
    
    if (isValid && !twoFA.enabled) {
      // Enable 2FA on first successful verification
      await this.db.query(
        'UPDATE two_factor_auth SET enabled = true WHERE user_id = $1',
        [userId]
      );
    }
    
    return isValid;
  }

  async refreshToken(refreshToken: string): Promise<AuthToken> {
    try {
      const decoded = jwt.verify(refreshToken, this.jwtRefreshSecret) as any;
      
      // Check if refresh token exists
      const tokenHash = this.hashToken(refreshToken);
      const query = 'SELECT * FROM auth_tokens WHERE refresh_token_hash = $1';
      const result = await this.db.query(query, [tokenHash]);
      
      if (result.rows.length === 0) {
        throw new AuthenticationError('Invalid refresh token');
      }
      
      // Generate new access token
      const token = jwt.sign(
        { userId: decoded.userId, deviceId: decoded.deviceId },
        this.jwtSecret,
        { expiresIn: '1h' }
      );
      
      // Update token in database
      const expiresAt = new Date(Date.now() + 3600000);
      const updateQuery = `
        UPDATE auth_tokens 
        SET token_hash = $1, expires_at = $2 
        WHERE refresh_token_hash = $3
        RETURNING *
      `;
      
      const updateResult = await this.db.query(updateQuery, [
        this.hashToken(token),
        expiresAt,
        tokenHash
      ]);
      
      const authToken = updateResult.rows[0];
      
      return {
        id: authToken.id,
        userId: authToken.user_id,
        deviceId: authToken.device_id,
        token,
        refreshToken,
        expiresAt,
        createdAt: new Date(authToken.created_at)
      };
    } catch (error) {
      throw new AuthenticationError('Invalid refresh token');
    }
  }

  private async registerDevice(userId: string, deviceFingerprint: string): Promise<string> {
    // Check if device exists
    const query = 'SELECT * FROM devices WHERE user_id = $1 AND device_fingerprint = $2';
    const result = await this.db.query(query, [userId, deviceFingerprint]);
    
    if (result.rows.length > 0) {
      // Update last activity
      await this.db.query(
        'UPDATE devices SET last_activity = NOW() WHERE id = $1',
        [result.rows[0].id]
      );
      return result.rows[0].id;
    }
    
    // Create new device
    const deviceId = uuidv4();
    const insertQuery = `
      INSERT INTO devices (id, user_id, device_fingerprint, trust_level, last_activity, created_at)
      VALUES ($1, $2, $3, 'untrusted', NOW(), NOW())
    `;
    
    await this.db.query(insertQuery, [deviceId, userId, deviceFingerprint]);
    
    return deviceId;
  }

  private hashToken(token: string): string {
    return require('crypto').createHash('sha256').update(token).digest('hex');
  }

  private mapToUser(row: any): User {
    return {
      id: row.id,
      email: row.email,
      displayName: row.display_name,
      isVerified: row.is_verified,
      lastSeen: row.last_seen ? new Date(row.last_seen) : undefined,
      createdAt: new Date(row.created_at),
      updatedAt: new Date(row.updated_at)
    };
  }
}