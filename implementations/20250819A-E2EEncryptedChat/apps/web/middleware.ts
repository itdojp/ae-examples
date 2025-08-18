import createMiddleware from 'next-intl/middleware';
import { NextRequest, NextResponse } from 'next/server';
import { setSecurityHeaders, generateNonce, checkRateLimit } from './lib/security';

const intlMiddleware = createMiddleware({
  // A list of all locales that are supported
  locales: ['ja', 'en'],
  
  // Used when no locale matches
  defaultLocale: 'ja'
});

export default function middleware(request: NextRequest) {
  const response = intlMiddleware(request);
  
  // Nonceの生成（CSP用）
  const nonce = generateNonce();
  response.headers.set('x-nonce', nonce);
  
  // セキュリティヘッダーの設定
  const secureResponse = setSecurityHeaders(response, nonce);
  
  // レート制限のチェック（セキュリティ関連のエンドポイント）
  const pathname = request.nextUrl.pathname;
  if (pathname.includes('/api/') || pathname.includes('/chat/') || pathname.includes('/verification/')) {
    const identifier = request.ip || request.headers.get('x-forwarded-for') || 'unknown';
    const rateLimit = checkRateLimit(identifier, 100, 60000); // 1分間に100リクエスト
    
    if (!rateLimit.allowed) {
      return new NextResponse('Rate limit exceeded', { 
        status: 429,
        headers: {
          'Retry-After': Math.ceil((rateLimit.resetTime - Date.now()) / 1000).toString(),
        },
      });
    }
    
    // レート制限ヘッダーの追加
    secureResponse.headers.set('X-RateLimit-Limit', '100');
    secureResponse.headers.set('X-RateLimit-Remaining', rateLimit.remaining.toString());
    secureResponse.headers.set('X-RateLimit-Reset', rateLimit.resetTime.toString());
  }
  
  // セキュアなパスでの追加チェック
  if (pathname.includes('/chat/') || pathname.includes('/settings/') || pathname.includes('/devices/')) {
    // 実際のプロダクションでは認証チェックを追加
    // const authResult = await checkAuthentication(request);
    // if (!authResult.authenticated) {
    //   return NextResponse.redirect(new URL('/login', request.url));
    // }
    
    // セキュアページ用の追加ヘッダー
    secureResponse.headers.set('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
    secureResponse.headers.set('Pragma', 'no-cache');
    secureResponse.headers.set('Expires', '0');
  }
  
  return secureResponse;
}

export const config = {
  // セキュリティミドルウェアを適用するパス
  matcher: [
    '/',
    '/(ja|en)/:path*',
    '/api/:path*',
    '/chat/:path*',
    '/verification/:path*',
    '/settings/:path*',
    '/devices/:path*'
  ]
};