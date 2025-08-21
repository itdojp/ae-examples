import { NextRequest, NextResponse } from 'next/server';

// CSPヘッダーの生成
export function generateCSPHeader(nonce: string): string {
  const cspDirectives = [
    "default-src 'self'",
    `script-src 'self' 'unsafe-eval' 'nonce-${nonce}' https://unpkg.com`, // Next.jsの動的インポート用
    `style-src 'self' 'unsafe-inline' https://fonts.googleapis.com`, // Tailwind CSSとGoogle Fonts用
    "font-src 'self' https://fonts.gstatic.com",
    "img-src 'self' data: https:",
    "connect-src 'self' wss: https:",
    "frame-ancestors 'none'",
    "base-uri 'self'",
    "form-action 'self'",
    "upgrade-insecure-requests",
  ];
  
  return cspDirectives.join('; ');
}

// セキュアなレスポンスヘッダーの設定
export function setSecurityHeaders(response: NextResponse, nonce?: string): NextResponse {
  // CSP (Content Security Policy)
  if (nonce) {
    response.headers.set('Content-Security-Policy', generateCSPHeader(nonce));
  }
  
  // XSS Protection
  response.headers.set('X-XSS-Protection', '1; mode=block');
  
  // Content Type Options
  response.headers.set('X-Content-Type-Options', 'nosniff');
  
  // Frame Options
  response.headers.set('X-Frame-Options', 'DENY');
  
  // Referrer Policy
  response.headers.set('Referrer-Policy', 'strict-origin-when-cross-origin');
  
  // Permissions Policy
  response.headers.set('Permissions-Policy', [
    'camera=()',
    'microphone=()',
    'geolocation=()',
    'interest-cohort=()',
    'payment=()',
    'usb=()',
  ].join(', '));
  
  // HSTS (HTTPS Strict Transport Security)
  response.headers.set('Strict-Transport-Security', 'max-age=31536000; includeSubDomains; preload');
  
  // CSRF Protection
  response.headers.set('X-CSRF-Token-Required', 'true');
  
  return response;
}

// CSRF Token生成
export function generateCSRFToken(): string {
  if (typeof crypto !== 'undefined' && crypto.randomUUID) {
    return crypto.randomUUID();
  }
  
  // Fallback for environments without crypto.randomUUID
  return Math.random().toString(36).substring(2, 15) + Math.random().toString(36).substring(2, 15);
}

// Nonce生成
export function generateNonce(): string {
  if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
    const array = new Uint8Array(16);
    crypto.getRandomValues(array);
    return Array.from(array, byte => byte.toString(16).padStart(2, '0')).join('');
  }
  
  // Fallback
  return Math.random().toString(36).substring(2, 15) + Math.random().toString(36).substring(2, 15);
}

// レート制限のチェック
interface RateLimitEntry {
  count: number;
  resetTime: number;
}

const rateLimitMap = new Map<string, RateLimitEntry>();

export function checkRateLimit(
  identifier: string,
  maxRequests: number,
  windowMs: number
): { allowed: boolean; remaining: number; resetTime: number } {
  const now = Date.now();
  const entry = rateLimitMap.get(identifier);
  
  if (!entry || now > entry.resetTime) {
    // 新しいウィンドウの開始
    const resetTime = now + windowMs;
    rateLimitMap.set(identifier, { count: 1, resetTime });
    return { allowed: true, remaining: maxRequests - 1, resetTime };
  }
  
  if (entry.count >= maxRequests) {
    return { allowed: false, remaining: 0, resetTime: entry.resetTime };
  }
  
  entry.count += 1;
  return { allowed: true, remaining: maxRequests - entry.count, resetTime: entry.resetTime };
}

// セキュリティ監査ログ
export interface SecurityAuditLog {
  timestamp: Date;
  userId?: string;
  action: string;
  resource: string;
  ipAddress: string;
  userAgent: string;
  success: boolean;
  details?: Record<string, any>;
}

export function createSecurityAuditLog(
  request: NextRequest,
  action: string,
  resource: string,
  success: boolean,
  userId?: string,
  details?: Record<string, any>
): SecurityAuditLog {
  return {
    timestamp: new Date(),
    userId,
    action,
    resource,
    ipAddress: request.ip || request.headers.get('x-forwarded-for') || 'unknown',
    userAgent: request.headers.get('user-agent') || 'unknown',
    success,
    details,
  };
}

// セキュアクッキーの設定
export function setSecureCookie(
  response: NextResponse,
  name: string,
  value: string,
  options: {
    maxAge?: number;
    httpOnly?: boolean;
    secure?: boolean;
    sameSite?: 'strict' | 'lax' | 'none';
    path?: string;
  } = {}
): NextResponse {
  const cookieOptions = {
    maxAge: 86400, // 24時間
    httpOnly: true,
    secure: process.env.NODE_ENV === 'production',
    sameSite: 'strict' as const,
    path: '/',
    ...options,
  };
  
  const cookieString = [
    `${name}=${value}`,
    `Max-Age=${cookieOptions.maxAge}`,
    cookieOptions.httpOnly && 'HttpOnly',
    cookieOptions.secure && 'Secure',
    `SameSite=${cookieOptions.sameSite}`,
    `Path=${cookieOptions.path}`,
  ].filter(Boolean).join('; ');
  
  response.headers.append('Set-Cookie', cookieString);
  return response;
}

// 入力の検証とサニタイゼーション
export function validateAndSanitizeInput(input: string, maxLength: number = 1000): {
  isValid: boolean;
  sanitized: string;
  errors: string[];
} {
  const errors: string[] = [];
  
  // 基本的な検証
  if (typeof input !== 'string') {
    errors.push('Input must be a string');
    return { isValid: false, sanitized: '', errors };
  }
  
  if (input.length > maxLength) {
    errors.push(`Input exceeds maximum length of ${maxLength} characters`);
  }
  
  // XSS対策のサニタイゼーション
  const sanitized = input
    .replace(/[<>\"']/g, '') // HTML特殊文字の除去
    .replace(/javascript:/gi, '') // JavaScriptプロトコルの除去
    .replace(/on\w+\s*=/gi, '') // イベントハンドラーの除去
    .trim();
  
  // SQLインジェクション対策の基本チェック
  const sqlPatterns = [
    /union\s+select/gi,
    /insert\s+into/gi,
    /delete\s+from/gi,
    /drop\s+table/gi,
    /alter\s+table/gi,
  ];
  
  for (const pattern of sqlPatterns) {
    if (pattern.test(sanitized)) {
      errors.push('Input contains potentially dangerous SQL patterns');
      break;
    }
  }
  
  return {
    isValid: errors.length === 0,
    sanitized,
    errors,
  };
}

// IPアドレスの検証
export function validateIPAddress(ip: string): boolean {
  // IPv4の正規表現
  const ipv4Regex = /^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/;
  
  // IPv6の基本的な正規表現（簡略化）
  const ipv6Regex = /^(?:[0-9a-fA-F]{1,4}:){7}[0-9a-fA-F]{1,4}$/;
  
  return ipv4Regex.test(ip) || ipv6Regex.test(ip);
}