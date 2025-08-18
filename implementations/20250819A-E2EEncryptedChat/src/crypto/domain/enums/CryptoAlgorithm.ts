/**
 * Enum: CryptoAlgorithm
 * 
 * サポートする暗号化アルゴリズムの定義
 * NIST承認アルゴリズムとSignal Protocol準拠アルゴリズムを含む
 */

export enum CryptoAlgorithm {
  // 対称暗号化
  AES_256_GCM = 'AES-256-GCM',
  ChaCha20_Poly1305 = 'ChaCha20-Poly1305',
  
  // 非対称暗号化・鍵交換
  X25519 = 'X25519',
  
  // デジタル署名
  Ed25519 = 'Ed25519',
  
  // HMAC
  HMAC_SHA256 = 'HMAC-SHA-256',
  HMAC_SHA512 = 'HMAC-SHA-512',
  
  // ハッシュ関数
  SHA256 = 'SHA-256',
  SHA512 = 'SHA-512'
}

export enum SecurityLevel {
  LOW = 'LOW',
  MEDIUM = 'MEDIUM', 
  HIGH = 'HIGH',
  WARNING = 'WARNING',
  ERROR = 'ERROR'
}