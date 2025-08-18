import { type ClassValue, clsx } from 'clsx';
import { twMerge } from 'tailwind-merge';

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

// セキュリティユーティリティ
export function sanitizeInput(input: string): string {
  return input
    .replace(/[<>\"']/g, '') // XSS対策
    .trim()
    .slice(0, 1000); // 入力長制限
}

export function generateSecureId(): string {
  return crypto.randomUUID();
}

export function validateSessionId(sessionId: string): boolean {
  const sessionIdRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/;
  return sessionIdRegex.test(sessionId);
}

// エラー境界用のヘルパー
export function createSecureErrorMessage(error: Error): string {
  // プロダクション環境では詳細なエラー情報を隠す
  if (process.env.NODE_ENV === 'production') {
    return 'An error occurred. Please try again.';
  }
  return error.message;
}