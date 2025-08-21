/**
 * OpenTelemetry Configuration for Secure Chat Application
 * 
 * セキュリティメトリクス、パフォーマンス監視、エラー追跡を統合
 * ae-framework Phase 6 品質ゲートとリアルタイム監視を実装
 */

import { NodeSDK } from '@opentelemetry/sdk-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';
import { OTLPMetricExporter } from '@opentelemetry/exporter-metrics-otlp-grpc';
import { PeriodicExportingMetricReader } from '@opentelemetry/sdk-metrics';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { trace, metrics, SpanStatusCode, SpanKind } from '@opentelemetry/api';

// Environment configuration
const TELEMETRY_CONFIG = {
  serviceName: 'ae-framework-secure-chat',
  serviceVersion: process.env.npm_package_version || '1.0.0',
  environment: process.env.NODE_ENV || 'development',
  otlpEndpoint: process.env.OTEL_EXPORTER_OTLP_ENDPOINT || 'http://localhost:4317',
  debugTelemetry: process.env.DEBUG_TELEMETRY === 'true',
  disableTelemetry: process.env.DISABLE_TELEMETRY === 'true',
  securityLevel: 'HIGH' // E2E Encryption
};

/**
 * OpenTelemetry SDK初期化
 */
export function initializeTelemetry() {
  if (TELEMETRY_CONFIG.disableTelemetry) {
    console.log('📊 OpenTelemetry disabled via DISABLE_TELEMETRY');
    return;
  }

  const traceExporter = new OTLPTraceExporter({
    url: `${TELEMETRY_CONFIG.otlpEndpoint}/v1/traces`,
  });

  const metricExporter = new OTLPMetricExporter({
    url: `${TELEMETRY_CONFIG.otlpEndpoint}/v1/metrics`,
  });

  const sdk = new NodeSDK({
    resource: new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: TELEMETRY_CONFIG.serviceName,
      [SemanticResourceAttributes.SERVICE_VERSION]: TELEMETRY_CONFIG.serviceVersion,
      [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: TELEMETRY_CONFIG.environment,
      // セキュリティコンテキスト
      'security.level': TELEMETRY_CONFIG.securityLevel,
      'crypto.protocol': 'Signal Protocol',
      'encryption.algorithm': 'AES-256-GCM',
    }),
    traceExporter,
    metricReader: new PeriodicExportingMetricReader({
      exporter: metricExporter,
      exportIntervalMillis: 5000, // 5秒間隔
    }),
    instrumentations: [getNodeAutoInstrumentations()],
  });

  sdk.start();

  // デバッグモードでのコンソール出力
  if (TELEMETRY_CONFIG.debugTelemetry) {
    console.log(`📊 OpenTelemetry initialized for ${TELEMETRY_CONFIG.serviceName}`);
    console.log(`   Service: ${TELEMETRY_CONFIG.serviceName} v${TELEMETRY_CONFIG.serviceVersion}`);
    console.log(`   Environment: ${TELEMETRY_CONFIG.environment}`);
    console.log(`   Security Level: ${TELEMETRY_CONFIG.securityLevel}`);
    console.log(`   OTLP Export: ${TELEMETRY_CONFIG.otlpEndpoint ? '✅ Enabled' : '❌ Disabled'}`);
  }

  // Graceful shutdown
  process.on('SIGTERM', () => {
    sdk.shutdown()
      .then(() => console.log('📊 OpenTelemetry terminated'))
      .catch((error) => console.error('❌ Error terminating OpenTelemetry', error))
      .finally(() => process.exit(0));
  });
}

/**
 * セキュリティメトリクスコレクター
 */
export class SecurityTelemetryCollector {
  private tracer = trace.getTracer('secure-chat-security', '1.0.0');
  private meter = metrics.getMeter('secure-chat-metrics', '1.0.0');

  // メトリクス定義
  private encryptionDuration = this.meter.createHistogram('encryption_duration_ms', {
    description: 'Time taken to encrypt a message',
    unit: 'ms',
  });

  private decryptionDuration = this.meter.createHistogram('decryption_duration_ms', {
    description: 'Time taken to decrypt a message',
    unit: 'ms',
  });

  private keyRotationCounter = this.meter.createCounter('key_rotations_total', {
    description: 'Total number of key rotations performed',
  });

  private authenticationFailures = this.meter.createCounter('authentication_failures_total', {
    description: 'Total authentication failures',
  });

  private sessionCreations = this.meter.createCounter('secure_sessions_created_total', {
    description: 'Total secure sessions created',
  });

  private messagesSent = this.meter.createCounter('encrypted_messages_sent_total', {
    description: 'Total encrypted messages sent',
  });

  private messagesReceived = this.meter.createCounter('encrypted_messages_received_total', {
    description: 'Total encrypted messages received',
  });

  private securityViolations = this.meter.createCounter('security_violations_total', {
    description: 'Total security violations detected',
  });

  private uiInteractions = this.meter.createCounter('ui_interactions_total', {
    description: 'Total UI interactions recorded',
  });

  // Phase 6品質ゲートメトリクス
  private testCoverage = this.meter.createGauge('test_coverage_percentage', {
    description: 'Current test coverage percentage',
  });

  private a11yScore = this.meter.createGauge('accessibility_score_percentage', {
    description: 'Current accessibility score percentage',
  });

  private performanceScore = this.meter.createGauge('performance_score_percentage', {
    description: 'Current performance score percentage',
  });

  private buildTime = this.meter.createHistogram('build_time_ms', {
    description: 'Application build time',
    unit: 'ms',
  });

  /**
   * 暗号化パフォーマンス記録
   */
  public recordEncryption(durationMs: number, messageSize: number, algorithm: string) {
    const sizeCategory = this.getMessageSizeCategory(messageSize);
    
    this.encryptionDuration.record(durationMs, {
      'encryption.algorithm': algorithm,
      'message.size_category': sizeCategory,
      'security.level': TELEMETRY_CONFIG.securityLevel,
    });

    // デバッグログ
    if (TELEMETRY_CONFIG.debugTelemetry) {
      console.log(`🔐 Encryption recorded: ${durationMs}ms (${sizeCategory}, ${algorithm})`);
    }
  }

  /**
   * 復号化パフォーマンス記録
   */
  public recordDecryption(durationMs: number, messageSize: number, success: boolean) {
    const sizeCategory = this.getMessageSizeCategory(messageSize);
    
    this.decryptionDuration.record(durationMs, {
      'message.size_category': sizeCategory,
      'decryption.success': success.toString(),
    });
  }

  /**
   * 鍵ローテーション記録
   */
  public recordKeyRotation(sessionId: string, rotationType: 'automatic' | 'manual' | 'security_incident') {
    this.keyRotationCounter.add(1, {
      'session.id': sessionId,
      'rotation.type': rotationType,
      'security.level': TELEMETRY_CONFIG.securityLevel,
    });

    if (TELEMETRY_CONFIG.debugTelemetry) {
      console.log(`🔄 Key rotation recorded: ${rotationType} for session ${sessionId}`);
    }
  }

  /**
   * 認証失敗記録
   */
  public recordAuthFailure(reason: string, userId?: string) {
    this.authenticationFailures.add(1, {
      'failure.reason': reason,
      'user.id': userId || 'unknown',
    });

    if (TELEMETRY_CONFIG.debugTelemetry) {
      console.log(`❌ Authentication failure: ${reason}`);
    }
  }

  /**
   * セキュアセッション作成記録
   */
  public recordSessionCreation(sessionId: string, participants: number) {
    this.sessionCreations.add(1, {
      'session.id': sessionId,
      'session.participants': participants.toString(),
      'encryption.enabled': 'true',
    });
  }

  /**
   * メッセージ送信記録
   */
  public recordMessageSent(sessionId: string, messageSize: number, encryptionAlgorithm: string) {
    this.messagesSent.add(1, {
      'session.id': sessionId,
      'message.size_category': this.getMessageSizeCategory(messageSize),
      'encryption.algorithm': encryptionAlgorithm,
    });
  }

  /**
   * メッセージ受信記録
   */
  public recordMessageReceived(sessionId: string, decryptionSuccess: boolean) {
    this.messagesReceived.add(1, {
      'session.id': sessionId,
      'decryption.success': decryptionSuccess.toString(),
    });
  }

  /**
   * セキュリティ違反記録
   */
  public recordSecurityViolation(violationType: string, severity: 'low' | 'medium' | 'high' | 'critical', details?: any) {
    this.securityViolations.add(1, {
      'violation.type': violationType,
      'violation.severity': severity,
    });

    // 重大度に応じたアラート
    if (severity === 'critical') {
      console.error(`🚨 CRITICAL Security Violation: ${violationType}`, details);
    }
  }

  /**
   * UIインタラクション記録
   */
  public recordUIInteraction(element: string, action: string, sessionId?: string) {
    this.uiInteractions.add(1, {
      'ui.element': element,
      'ui.action': action,
      'session.id': sessionId || 'none',
    });
  }

  /**
   * Phase 6品質ゲート記録
   */
  public recordQualityGate(
    testCoverage: number,
    a11yScore: number,
    performanceScore: number,
    buildTimeMs?: number
  ) {
    this.testCoverage.record(testCoverage, {
      'quality.gate': 'test_coverage',
      'quality.threshold': '80',
    });

    this.a11yScore.record(a11yScore, {
      'quality.gate': 'accessibility',
      'quality.threshold': '95',
    });

    this.performanceScore.record(performanceScore, {
      'quality.gate': 'performance',  
      'quality.threshold': '75',
    });

    if (buildTimeMs) {
      this.buildTime.record(buildTimeMs, {
        'build.type': 'production',
      });
    }

    // 品質ゲート結果ログ
    if (TELEMETRY_CONFIG.debugTelemetry) {
      const coverageStatus = testCoverage >= 80 ? '✅' : '❌';
      const a11yStatus = a11yScore >= 95 ? '✅' : '❌'; 
      const perfStatus = performanceScore >= 75 ? '✅' : '❌';

      console.log(`📊 Phase 6 Quality Gates:`);
      console.log(`   📊 Test Coverage: ${testCoverage}% (threshold: 80%) ${coverageStatus}`);
      console.log(`   ♿ A11y Score: ${a11yScore}% (threshold: 95%) ${a11yStatus}`);
      console.log(`   ⚡ Performance Score: ${performanceScore}% (threshold: 75%) ${perfStatus}`);
      if (buildTimeMs) {
        console.log(`   🏗️ Build Time: ${buildTimeMs}ms`);
      }
    }
  }

  /**
   * セキュリティスパン作成
   */
  public createSecuritySpan(name: string, attributes?: any) {
    return this.tracer.startSpan(name, {
      kind: SpanKind.INTERNAL,
      attributes: {
        'security.operation': name,
        'security.level': TELEMETRY_CONFIG.securityLevel,
        ...attributes,
      },
    });
  }

  /**
   * エラースパン記録
   */
  public recordError(span: any, error: Error, severity: 'low' | 'medium' | 'high' | 'critical' = 'medium') {
    span.recordException(error);
    span.setStatus({
      code: SpanStatusCode.ERROR,
      message: error.message,
    });
    span.setAttributes({
      'error.type': error.name,
      'error.severity': severity,
    });
  }

  /**
   * メッセージサイズカテゴリ分類
   */
  private getMessageSizeCategory(sizeBytes: number): string {
    if (sizeBytes < 1024) return 'small';        // < 1KB
    if (sizeBytes < 10240) return 'medium';      // < 10KB
    if (sizeBytes < 102400) return 'large';      // < 100KB
    return 'xlarge';                             // >= 100KB
  }
}

// グローバルインスタンス
export const securityTelemetry = new SecurityTelemetryCollector();

/**
 * Phase 6効率性メトリクス
 */
export class Phase6EfficiencyCollector {
  private meter = metrics.getMeter('phase6-efficiency', '1.0.0');

  private scaffoldTime = this.meter.createHistogram('ui_scaffold_time_ms', {
    description: 'Time taken to scaffold UI components',
    unit: 'ms',
  });

  private componentCount = this.meter.createCounter('generated_components_total', {
    description: 'Total UI components generated',
  });

  private e2eTestTime = this.meter.createHistogram('e2e_test_duration_ms', {
    description: 'End-to-end test execution time',
    unit: 'ms',
  });

  public recordScaffoldTime(durationMs: number, componentCount: number, entityCount: number) {
    this.scaffoldTime.record(durationMs, {
      'scaffold.type': 'ui_components',
      'component.count': componentCount.toString(),
      'entity.count': entityCount.toString(),
    });

    this.componentCount.add(componentCount, {
      'generation.type': 'automated',
    });

    if (TELEMETRY_CONFIG.debugTelemetry) {
      console.log(`📈 Phase 6 Efficiency Metrics:`);
      console.log(`  🏗️  Scaffold Time: ${durationMs}ms ${durationMs < 30000 ? '✅' : '⚠️'}`);
      console.log(`  📊 Generated ${componentCount} files for ${entityCount}/${entityCount} entities`);
    }
  }

  public recordE2ETestTime(durationMs: number, testCount: number, passRate: number) {
    this.e2eTestTime.record(durationMs, {
      'test.count': testCount.toString(),
      'test.pass_rate': passRate.toString(),
    });
  }
}

export const phase6Metrics = new Phase6EfficiencyCollector();

/**
 * React Hook for Security Telemetry
 */
export function useSecurityTelemetry() {
  return {
    recordSecurityEvent: (event: {
      type: string;
      sessionId: string;
      userId: string;
      timestamp: Date;
      details?: any;
    }) => {
      const span = securityTelemetry.createSecuritySpan(`security.${event.type}`, {
        'session.id': event.sessionId,
        'user.id': event.userId,
        ...event.details,
      });
      
      span.end();
    },

    recordUIInteraction: (interaction: {
      element: string;
      action: string;
      sessionId: string;
      timestamp: Date;
    }) => {
      securityTelemetry.recordUIInteraction(
        interaction.element,
        interaction.action,
        interaction.sessionId
      );
    },

    recordPerformanceMetric: (metric: {
      operation: string;
      durationMs: number;
      success: boolean;
      details?: any;
    }) => {
      if (metric.operation.includes('encrypt')) {
        securityTelemetry.recordEncryption(
          metric.durationMs,
          metric.details?.messageSize || 0,
          metric.details?.algorithm || 'AES-256-GCM'
        );
      } else if (metric.operation.includes('decrypt')) {
        securityTelemetry.recordDecryption(
          metric.durationMs,
          metric.details?.messageSize || 0,
          metric.success
        );
      }
    },
  };
}

// 初期化の実行（本番環境）
if (typeof window === 'undefined' && process.env.NODE_ENV === 'production') {
  initializeTelemetry();
}