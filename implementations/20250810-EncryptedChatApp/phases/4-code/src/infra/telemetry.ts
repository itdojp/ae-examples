import { NodeSDK } from '@opentelemetry/sdk-node';
import { getNodeAutoInstrumentations } from '@opentelemetry/auto-instrumentations-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';
import { OTLPMetricExporter } from '@opentelemetry/exporter-metrics-otlp-grpc';
import { PeriodicExportingMetricReader, MeterProvider, Counter, Histogram } from '@opentelemetry/sdk-metrics';
import { trace, context, SpanStatusCode, SpanKind } from '@opentelemetry/api';
import { JaegerExporter } from '@opentelemetry/exporter-jaeger';
import { PrometheusExporter } from '@opentelemetry/exporter-prometheus';
import { config } from '../config';

// Telemetry singleton
let telemetryInstance: TelemetryService | null = null;

export class TelemetryService {
  private sdk: NodeSDK;
  private meterProvider?: MeterProvider;
  private messageCounter?: Counter;
  private encryptionHistogram?: Histogram;
  private decryptionHistogram?: Histogram;
  private sessionCounter?: Counter;
  private authCounter?: Counter;
  private errorCounter?: Counter;
  private wsConnectionGauge?: any;

  constructor(serviceName: string = 'e2e-chat') {
    const resource = new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: serviceName,
      [SemanticResourceAttributes.SERVICE_VERSION]: process.env.SERVICE_VERSION || '1.0.0',
      [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: config.nodeEnv,
      'service.namespace': 'e2e-chat',
      'service.instance.id': process.env.HOSTNAME || 'localhost',
    });

    // Configure trace exporters
    const traceExporters: any[] = [];
    
    if (config.otel.endpoint) {
      traceExporters.push(new OTLPTraceExporter({
        url: config.otel.endpoint,
        headers: config.otel.headers ? JSON.parse(config.otel.headers) : undefined,
      }));
    }
    
    if (config.jaeger.endpoint) {
      traceExporters.push(new JaegerExporter({
        endpoint: config.jaeger.endpoint,
        serviceName,
      }));
    }

    // Configure metric exporters
    const metricExporters: any[] = [];
    
    if (config.otel.endpoint) {
      metricExporters.push(new OTLPMetricExporter({
        url: config.otel.endpoint,
        headers: config.otel.headers ? JSON.parse(config.otel.headers) : undefined,
      }));
    }
    
    // Prometheus exporter for metrics scraping
    const prometheusExporter = new PrometheusExporter({
      port: config.monitoring.prometheusPort,
      endpoint: '/metrics',
    }, () => {
      console.log(`Prometheus metrics available at http://localhost:${config.monitoring.prometheusPort}/metrics`);
    });

    this.sdk = new NodeSDK({
      resource,
      traceExporter: traceExporters.length > 0 ? traceExporters[0] : undefined,
      metricReader: new PeriodicExportingMetricReader({
        exporter: metricExporters.length > 0 ? metricExporters[0] : prometheusExporter,
        exportIntervalMillis: 10000,
      }),
      instrumentations: [
        getNodeAutoInstrumentations({
          '@opentelemetry/instrumentation-fs': {
            enabled: false,
          },
          '@opentelemetry/instrumentation-http': {
            requestHook: (span, request) => {
              span.setAttribute('http.request.body.size', request.headers['content-length'] || 0);
            },
            responseHook: (span, response) => {
              span.setAttribute('http.response.body.size', response.headers['content-length'] || 0);
            },
          },
          '@opentelemetry/instrumentation-fastify': {
            enabled: true,
          },
          '@opentelemetry/instrumentation-pg': {
            enabled: true,
          },
          '@opentelemetry/instrumentation-redis': {
            enabled: true,
          },
        }),
      ],
    });

    this.sdk.start();
    this.initializeMetrics();
  }

  private initializeMetrics() {
    const meter = this.sdk['_meterProvider']?.getMeter('e2e-chat-metrics');
    
    if (meter) {
      // Message metrics
      this.messageCounter = meter.createCounter('messages_total', {
        description: 'Total number of messages processed',
      });
      
      this.encryptionHistogram = meter.createHistogram('encryption_duration_ms', {
        description: 'Time taken to encrypt messages in milliseconds',
      });
      
      this.decryptionHistogram = meter.createHistogram('decryption_duration_ms', {
        description: 'Time taken to decrypt messages in milliseconds',
      });
      
      // Session metrics
      this.sessionCounter = meter.createCounter('sessions_total', {
        description: 'Total number of sessions established',
      });
      
      // Authentication metrics
      this.authCounter = meter.createCounter('auth_attempts_total', {
        description: 'Total number of authentication attempts',
      });
      
      // Error metrics
      this.errorCounter = meter.createCounter('errors_total', {
        description: 'Total number of errors',
      });
      
      // WebSocket metrics
      this.wsConnectionGauge = meter.createUpDownCounter('ws_connections', {
        description: 'Current number of WebSocket connections',
      });
    }
  }

  // Tracing helpers
  createSpan(name: string, kind: SpanKind = SpanKind.INTERNAL) {
    const tracer = trace.getTracer('e2e-chat');
    return tracer.startSpan(name, { kind });
  }

  async traceAsync<T>(
    name: string,
    fn: () => Promise<T>,
    attributes?: Record<string, any>
  ): Promise<T> {
    const span = this.createSpan(name);
    
    if (attributes) {
      Object.entries(attributes).forEach(([key, value]) => {
        span.setAttribute(key, value);
      });
    }
    
    try {
      const result = await fn();
      span.setStatus({ code: SpanStatusCode.OK });
      return result;
    } catch (error: any) {
      span.setStatus({
        code: SpanStatusCode.ERROR,
        message: error.message,
      });
      span.recordException(error);
      throw error;
    } finally {
      span.end();
    }
  }

  // Metric recording methods
  recordMessage(type: 'sent' | 'received' | 'encrypted' | 'decrypted', attributes?: Record<string, any>) {
    this.messageCounter?.add(1, { type, ...attributes });
  }

  recordEncryption(durationMs: number, attributes?: Record<string, any>) {
    this.encryptionHistogram?.record(durationMs, attributes);
  }

  recordDecryption(durationMs: number, attributes?: Record<string, any>) {
    this.decryptionHistogram?.record(durationMs, attributes);
  }

  recordSession(type: 'established' | 'terminated', attributes?: Record<string, any>) {
    this.sessionCounter?.add(1, { type, ...attributes });
  }

  recordAuth(success: boolean, method: string, attributes?: Record<string, any>) {
    this.authCounter?.add(1, { success, method, ...attributes });
  }

  recordError(type: string, attributes?: Record<string, any>) {
    this.errorCounter?.add(1, { type, ...attributes });
  }

  recordWsConnection(delta: number) {
    this.wsConnectionGauge?.add(delta);
  }

  // Custom span for cryptographic operations
  traceCryptoOperation<T>(
    operation: string,
    fn: () => T,
    attributes?: Record<string, any>
  ): T {
    const span = this.createSpan(`crypto.${operation}`);
    span.setAttribute('crypto.operation', operation);
    
    if (attributes) {
      Object.entries(attributes).forEach(([key, value]) => {
        span.setAttribute(`crypto.${key}`, value);
      });
    }
    
    const startTime = Date.now();
    
    try {
      const result = fn();
      const duration = Date.now() - startTime;
      
      span.setAttribute('crypto.duration_ms', duration);
      span.setStatus({ code: SpanStatusCode.OK });
      
      if (operation === 'encrypt') {
        this.recordEncryption(duration, attributes);
      } else if (operation === 'decrypt') {
        this.recordDecryption(duration, attributes);
      }
      
      return result;
    } catch (error: any) {
      span.setStatus({
        code: SpanStatusCode.ERROR,
        message: error.message,
      });
      span.recordException(error);
      this.recordError('crypto', { operation, ...attributes });
      throw error;
    } finally {
      span.end();
    }
  }

  async shutdown() {
    await this.sdk.shutdown();
    console.log('Telemetry shutdown complete');
  }
}

export function initTelemetry(serviceName?: string) {
  if (!telemetryInstance) {
    telemetryInstance = new TelemetryService(serviceName);
    
    // Graceful shutdown
    process.on('SIGTERM', async () => {
      if (telemetryInstance) {
        await telemetryInstance.shutdown();
      }
    });
    
    process.on('SIGINT', async () => {
      if (telemetryInstance) {
        await telemetryInstance.shutdown();
      }
    });
  }
  
  return telemetryInstance;
}

export function getTelemetry(): TelemetryService {
  if (!telemetryInstance) {
    throw new Error('Telemetry not initialized. Call initTelemetry() first.');
  }
  return telemetryInstance;
}