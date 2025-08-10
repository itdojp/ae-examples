import { z } from 'zod';
import dotenv from 'dotenv';
import path from 'path';

// Load environment variables
const envFile = process.env.NODE_ENV === 'test' ? '.env.test' : '.env';
dotenv.config({ path: path.resolve(process.cwd(), envFile) });

// Environment schema
const ConfigSchema = z.object({
  // Node Environment
  nodeEnv: z.enum(['development', 'test', 'production']).default('development'),
  
  // Server Configuration
  server: z.object({
    port: z.number().min(1).max(65535).default(3000),
    host: z.string().default('0.0.0.0'),
    apiUrl: z.string().url().default('http://localhost:3000'),
    wsUrl: z.string().default('ws://localhost:3000'),
  }),
  
  // Database Configuration
  database: z.object({
    url: z.string(),
    poolSize: z.number().min(1).max(100).default(20),
    timeout: z.number().min(1000).default(10000),
  }),
  
  // Redis Configuration
  redis: z.object({
    url: z.string().default('redis://localhost:6379'),
    password: z.string().optional(),
    db: z.number().min(0).max(15).default(0),
    timeout: z.number().min(1000).default(5000),
  }),
  
  // Security Configuration
  security: z.object({
    jwtSecret: z.string().min(32),
    jwtExpiresIn: z.string().default('7d'),
    refreshTokenExpiresIn: z.string().default('30d'),
    encryptionKey: z.string().min(32),
    bcryptRounds: z.number().min(10).max(20).default(12),
  }),
  
  // 2FA Configuration
  twoFA: z.object({
    issuer: z.string().default('E2E-Chat'),
    window: z.number().min(0).max(10).default(1),
  }),
  
  // CORS Configuration
  cors: z.object({
    origin: z.union([z.string(), z.array(z.string()), z.boolean()]).default('*'),
    credentials: z.boolean().default(true),
  }),
  
  // Rate Limiting
  rateLimit: z.object({
    windowMs: z.number().min(1000).default(60000),
    maxRequests: z.number().min(1).default(100),
  }),
  
  // Logging Configuration
  logging: z.object({
    level: z.enum(['error', 'warn', 'info', 'debug', 'trace']).default('info'),
    format: z.enum(['json', 'pretty']).default('json'),
    file: z.string().optional(),
    maxSize: z.string().default('10m'),
    maxFiles: z.number().default(10),
    compress: z.boolean().default(true),
  }),
  
  // OpenTelemetry Configuration
  otel: z.object({
    serviceName: z.string().default('e2e-chat'),
    endpoint: z.string().optional(),
    headers: z.string().optional(),
    tracesEnabled: z.boolean().default(true),
    metricsEnabled: z.boolean().default(true),
    logsEnabled: z.boolean().default(true),
    samplingRatio: z.number().min(0).max(1).default(1.0),
  }),
  
  // Jaeger Configuration
  jaeger: z.object({
    endpoint: z.string().optional(),
    agentHost: z.string().optional(),
    agentPort: z.number().optional(),
  }),
  
  // OPA Configuration
  opa: z.object({
    url: z.string().default('http://localhost:8181'),
    policyPath: z.string().default('/v1/data/e2echat'),
    timeout: z.number().default(5000),
  }),
  
  // Message Configuration
  message: z.object({
    maxSize: z.number().min(1).default(10485760), // 10MB
    retentionDays: z.number().min(1).default(90),
    cleanupInterval: z.number().min(60000).default(86400000), // 24 hours
  }),
  
  // Key Management
  keys: z.object({
    rotationInterval: z.number().min(3600000).default(604800000), // 7 days
    oneTimeKeysMin: z.number().min(10).default(100),
    oneTimeKeysBatch: z.number().min(10).default(100),
    signedPreKeyLifetime: z.number().min(86400000).default(2592000000), // 30 days
  }),
  
  // WebSocket Configuration
  ws: z.object({
    heartbeatInterval: z.number().min(5000).default(30000),
    maxConnections: z.number().min(1).default(10000),
    maxMessageSize: z.number().min(1024).default(1048576), // 1MB
  }),
  
  // File Upload Configuration
  upload: z.object({
    maxSize: z.number().min(1).default(104857600), // 100MB
    allowedTypes: z.array(z.string()).default([
      'image/jpeg',
      'image/png',
      'image/gif',
      'image/webp',
      'application/pdf'
    ]),
    storagePath: z.string().default('/app/uploads'),
  }),
  
  // Email Configuration
  email: z.object({
    smtp: z.object({
      host: z.string().optional(),
      port: z.number().default(587),
      secure: z.boolean().default(false),
      user: z.string().optional(),
      password: z.string().optional(),
    }).optional(),
    from: z.string().email().default('noreply@e2echat.local'),
  }),
  
  // Push Notifications
  push: z.object({
    fcm: z.object({
      serverKey: z.string().optional(),
    }).optional(),
    apns: z.object({
      keyId: z.string().optional(),
      teamId: z.string().optional(),
      bundleId: z.string().optional(),
    }).optional(),
  }),
  
  // Feature Flags
  features: z.object({
    twoFAEnabled: z.boolean().default(true),
    messageReactions: z.boolean().default(false),
    fileSharing: z.boolean().default(false),
    groupChat: z.boolean().default(false),
    voiceCalls: z.boolean().default(false),
    videoCalls: z.boolean().default(false),
  }),
  
  // Monitoring
  monitoring: z.object({
    sentryDsn: z.string().optional(),
    prometheusPort: z.number().default(9464),
    healthCheckInterval: z.number().default(30000),
  }),
  
  // Development/Debug
  debug: z.object({
    enabled: z.boolean().default(false),
    verboseLogging: z.boolean().default(false),
    sqlLogging: z.boolean().default(false),
  }),
});

// Parse and validate configuration
function loadConfig() {
  const config = {
    nodeEnv: process.env.NODE_ENV,
    
    server: {
      port: parseInt(process.env.PORT || '3000'),
      host: process.env.HOST,
      apiUrl: process.env.API_URL,
      wsUrl: process.env.WS_URL,
    },
    
    database: {
      url: process.env.DATABASE_URL,
      poolSize: parseInt(process.env.DATABASE_POOL_SIZE || '20'),
      timeout: parseInt(process.env.DATABASE_TIMEOUT || '10000'),
    },
    
    redis: {
      url: process.env.REDIS_URL,
      password: process.env.REDIS_PASSWORD,
      db: parseInt(process.env.REDIS_DB || '0'),
      timeout: parseInt(process.env.REDIS_TIMEOUT || '5000'),
    },
    
    security: {
      jwtSecret: process.env.JWT_SECRET || 'development-secret-change-in-production',
      jwtExpiresIn: process.env.JWT_EXPIRES_IN,
      refreshTokenExpiresIn: process.env.REFRESH_TOKEN_EXPIRES_IN,
      encryptionKey: process.env.ENCRYPTION_KEY || 'development-key-change-in-production',
      bcryptRounds: parseInt(process.env.BCRYPT_ROUNDS || '12'),
    },
    
    twoFA: {
      issuer: process.env.TOTP_ISSUER,
      window: parseInt(process.env.TOTP_WINDOW || '1'),
    },
    
    cors: {
      origin: process.env.CORS_ORIGIN === '*' ? '*' : 
              process.env.CORS_ORIGIN?.split(',') || '*',
      credentials: process.env.CORS_CREDENTIALS === 'true',
    },
    
    rateLimit: {
      windowMs: parseInt(process.env.RATE_LIMIT_WINDOW || '60000'),
      maxRequests: parseInt(process.env.RATE_LIMIT_MAX_REQUESTS || '100'),
    },
    
    logging: {
      level: process.env.LOG_LEVEL as any,
      format: process.env.LOG_FORMAT as any,
      file: process.env.LOG_FILE,
      maxSize: process.env.LOG_MAX_SIZE,
      maxFiles: parseInt(process.env.LOG_MAX_FILES || '10'),
      compress: process.env.LOG_COMPRESS === 'true',
    },
    
    otel: {
      serviceName: process.env.OTEL_SERVICE_NAME,
      endpoint: process.env.OTEL_EXPORTER_OTLP_ENDPOINT,
      headers: process.env.OTEL_EXPORTER_OTLP_HEADERS,
      tracesEnabled: process.env.OTEL_TRACES_ENABLED !== 'false',
      metricsEnabled: process.env.OTEL_METRICS_ENABLED !== 'false',
      logsEnabled: process.env.OTEL_LOGS_ENABLED !== 'false',
      samplingRatio: parseFloat(process.env.OTEL_SAMPLING_RATIO || '1.0'),
    },
    
    jaeger: {
      endpoint: process.env.JAEGER_ENDPOINT,
      agentHost: process.env.JAEGER_AGENT_HOST,
      agentPort: process.env.JAEGER_AGENT_PORT ? 
                 parseInt(process.env.JAEGER_AGENT_PORT) : undefined,
    },
    
    opa: {
      url: process.env.OPA_URL,
      policyPath: process.env.OPA_POLICY_PATH,
      timeout: parseInt(process.env.OPA_TIMEOUT || '5000'),
    },
    
    message: {
      maxSize: parseInt(process.env.MESSAGE_MAX_SIZE || '10485760'),
      retentionDays: parseInt(process.env.MESSAGE_RETENTION_DAYS || '90'),
      cleanupInterval: parseInt(process.env.MESSAGE_CLEANUP_INTERVAL || '86400000'),
    },
    
    keys: {
      rotationInterval: parseInt(process.env.KEY_ROTATION_INTERVAL || '604800000'),
      oneTimeKeysMin: parseInt(process.env.ONE_TIME_KEYS_MIN || '100'),
      oneTimeKeysBatch: parseInt(process.env.ONE_TIME_KEYS_BATCH || '100'),
      signedPreKeyLifetime: parseInt(process.env.SIGNED_PRE_KEY_LIFETIME || '2592000000'),
    },
    
    ws: {
      heartbeatInterval: parseInt(process.env.WS_HEARTBEAT_INTERVAL || '30000'),
      maxConnections: parseInt(process.env.WS_MAX_CONNECTIONS || '10000'),
      maxMessageSize: parseInt(process.env.WS_MAX_MESSAGE_SIZE || '1048576'),
    },
    
    upload: {
      maxSize: parseInt(process.env.UPLOAD_MAX_SIZE || '104857600'),
      allowedTypes: process.env.UPLOAD_ALLOWED_TYPES?.split(',') || [
        'image/jpeg',
        'image/png',
        'image/gif',
        'image/webp',
        'application/pdf'
      ],
      storagePath: process.env.UPLOAD_STORAGE_PATH,
    },
    
    email: {
      smtp: process.env.SMTP_HOST ? {
        host: process.env.SMTP_HOST,
        port: parseInt(process.env.SMTP_PORT || '587'),
        secure: process.env.SMTP_SECURE === 'true',
        user: process.env.SMTP_USER,
        password: process.env.SMTP_PASSWORD,
      } : undefined,
      from: process.env.EMAIL_FROM,
    },
    
    push: {
      fcm: process.env.FCM_SERVER_KEY ? {
        serverKey: process.env.FCM_SERVER_KEY,
      } : undefined,
      apns: process.env.APNS_KEY_ID ? {
        keyId: process.env.APNS_KEY_ID,
        teamId: process.env.APNS_TEAM_ID,
        bundleId: process.env.APNS_BUNDLE_ID,
      } : undefined,
    },
    
    features: {
      twoFAEnabled: process.env.FEATURE_2FA_ENABLED !== 'false',
      messageReactions: process.env.FEATURE_MESSAGE_REACTIONS === 'true',
      fileSharing: process.env.FEATURE_FILE_SHARING === 'true',
      groupChat: process.env.FEATURE_GROUP_CHAT === 'true',
      voiceCalls: process.env.FEATURE_VOICE_CALLS === 'true',
      videoCalls: process.env.FEATURE_VIDEO_CALLS === 'true',
    },
    
    monitoring: {
      sentryDsn: process.env.SENTRY_DSN,
      prometheusPort: parseInt(process.env.PROMETHEUS_PORT || '9464'),
      healthCheckInterval: parseInt(process.env.HEALTH_CHECK_INTERVAL || '30000'),
    },
    
    debug: {
      enabled: process.env.DEBUG === 'true',
      verboseLogging: process.env.VERBOSE_LOGGING === 'true',
      sqlLogging: process.env.SQL_LOGGING === 'true',
    },
  };
  
  // Validate configuration
  const result = ConfigSchema.safeParse(config);
  
  if (!result.success) {
    console.error('Configuration validation failed:', result.error.errors);
    throw new Error('Invalid configuration');
  }
  
  return result.data;
}

// Export validated configuration
export const config = loadConfig();

// Type export for TypeScript
export type Config = z.infer<typeof ConfigSchema>;