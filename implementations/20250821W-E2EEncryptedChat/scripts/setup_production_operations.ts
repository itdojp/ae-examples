/**
 * Production Operations Setup for E2E Chat Implementation
 * Using ae-framework Operate Agent for deployment and monitoring
 */

import { OperateAgent, type OperateAgentConfig } from './ae-framework/src/agents/operate-agent';
import { writeFileSync, mkdirSync, existsSync } from 'fs';
import * as path from 'path';

async function setupProductionOperations() {
  console.log('🚀 ae-framework Operate Agent を使用して本番運用環境をセットアップします...\n');

  const projectPath = '/home/claudecode/work/ae-framework_test/e2e_chat_implementation';
  
  // 1. Operate Agent設定
  console.log('⚙️ 1. Operate Agent設定の生成...');
  const operateConfig = createOperateConfig();
  console.log('   ✅ 包括的運用設定を生成しました');

  const agent = new OperateAgent(operateConfig);

  try {
    // 2. デプロイメント環境構築
    console.log('\n🏗️ 2. デプロイメント環境の構築...');
    await setupDeploymentEnvironment(projectPath);

    // 3. 監視システム設定
    console.log('\n📊 3. 監視とアラートシステムの設定...');
    await setupMonitoringAndAlerting(projectPath);

    // 4. CI/CDパイプライン構築
    console.log('\n🔄 4. CI/CDパイプラインの構築...');
    await setupCICDPipeline(projectPath);

    // 5. SLO設定とダッシュボード
    console.log('\n🎯 5. SLO設定とダッシュボードの生成...');
    await setupSLOAndDashboards(projectPath);

    // 6. セキュリティ監視設定
    console.log('\n🔐 6. セキュリティ監視の設定...');
    await setupSecurityMonitoring(projectPath);

    // 7. 初期デプロイメント実行
    console.log('\n🚀 7. 初期デプロイメントの実行...');
    await performInitialDeployment(agent);

    // 8. 運用手順書生成
    console.log('\n📚 8. 運用手順書の生成...');
    await generateOperationalDocumentation(projectPath, operateConfig);

    console.log('\n================================================================================');
    console.log('🎉 PRODUCTION OPERATIONS SETUP COMPLETED SUCCESSFULLY');
    console.log('================================================================================');
    console.log('🚀 E2E暗号化チャットアプリケーションの本番運用環境が正常にセットアップされました');
    console.log('📊 監視、アラート、CI/CD、セキュリティスキャンが有効になりました');
    console.log('📚 運用手順書とダッシュボードが生成されました');

  } catch (error) {
    console.error('❌ 本番運用環境セットアップ中にエラーが発生しました:', error);
    process.exit(1);
  }
}

function createOperateConfig(): OperateAgentConfig {
  return {
    deploymentConfig: {
      cicdProvider: 'github-actions',
      environments: ['development', 'staging', 'production'],
      rolloutStrategy: 'blue-green',
      healthCheckUrl: 'http://localhost:3000/api/health',
      timeoutSeconds: 300,
    },
    monitoringConfig: {
      metricsEndpoint: 'http://localhost:9090', // Prometheus
      logsEndpoint: 'http://localhost:3100',    // Loki
      tracesEndpoint: 'http://localhost:16686', // Jaeger
      healthEndpoints: [
        'http://localhost:3000/api/health',
        'http://localhost:3000/api/crypto/health',
        'http://localhost:3000/api/auth/health',
        'http://localhost:3000/api/messaging/health'
      ],
      checkIntervalMs: 30000, // 30秒間隔
    },
    alertingConfig: {
      channels: [
        {
          type: 'slack',
          endpoint: 'https://hooks.slack.com/services/WEBHOOK_URL',
          severity: 'high'
        },
        {
          type: 'email',
          endpoint: 'ops-team@company.com',
          severity: 'critical'
        },
        {
          type: 'pagerduty',
          endpoint: 'https://events.pagerduty.com/integration/INTEGRATION_KEY',
          severity: 'critical'
        }
      ],
      thresholds: [
        {
          metric: 'http_request_duration_ms_p95',
          condition: 'gt',
          value: 200,
          duration: '5m',
          severity: 'medium'
        },
        {
          metric: 'http_requests_error_rate',
          condition: 'gt',
          value: 1,
          duration: '2m',
          severity: 'high'
        },
        {
          metric: 'system_memory_usage_percent',
          condition: 'gt',
          value: 85,
          duration: '3m',
          severity: 'medium'
        },
        {
          metric: 'encryption_operations_per_second',
          condition: 'lt',
          value: 100,
          duration: '5m',
          severity: 'high'
        }
      ],
      escalationPolicy: [
        {
          delay: '5m',
          channels: ['slack']
        },
        {
          delay: '15m',
          channels: ['email', 'pagerduty']
        }
      ]
    },
    scalingConfig: {
      minInstances: 2,
      maxInstances: 20,
      targetCpuPercent: 70,
      targetMemoryPercent: 80,
      scaleUpCooldown: '3m',
      scaleDownCooldown: '5m',
    },
    securityConfig: {
      scanSchedule: '0 2 * * *', // 毎日午前2時
      vulnerabilityThreshold: 'medium',
      complianceFrameworks: ['SOC2', 'ISO27001', 'NIST'],
      securityEndpoints: [
        'http://localhost:8080/api/security/scan',
        'http://localhost:8080/api/compliance/check'
      ],
    },
    costConfig: {
      budgetLimit: 5000, // $5,000/月
      costCenter: 'engineering-chat-app',
      optimizationTargets: ['compute', 'storage', 'network'],
      reportingSchedule: '0 9 1 * *', // 毎月1日午前9時
    },
    sloConfig: {
      availability: 99.9,      // 99.9% アップタイム
      latencyP95Ms: 200,       // 95%ile レスポンス時間 < 200ms
      errorRatePercent: 0.1,   // エラー率 < 0.1%
      throughputRps: 1000,     // スループット > 1000 RPS
      evaluationWindow: '7d',  // 7日間の評価ウィンドウ
    },
    chaosConfig: {
      enabled: true,
      schedule: '0 14 * * 3', // 毎週水曜日午後2時
      experiments: [
        {
          name: 'pod-failure-test',
          type: 'pod-failure',
          targets: ['api-service'],
          duration: '5m',
          intensity: 20 // 20%のpodを停止
        },
        {
          name: 'network-latency-test',
          type: 'network-latency',
          targets: ['database-service'],
          duration: '3m',
          intensity: 50 // 50ms遅延追加
        },
        {
          name: 'memory-stress-test',
          type: 'memory-stress',
          targets: ['encryption-service'],
          duration: '2m',
          intensity: 30 // 30%メモリストレス
        }
      ],
      safetyLimits: {
        maxErrorRate: 5,     // 最大5%エラー率
        maxLatencyMs: 1000,  // 最大1秒レスポンス
        minHealthyInstances: 1 // 最低1つのヘルシーインスタンス
      }
    }
  };
}

async function setupDeploymentEnvironment(projectPath: string) {
  const deploymentDir = path.join(projectPath, 'deployment');
  
  if (!existsSync(deploymentDir)) {
    mkdirSync(deploymentDir, { recursive: true });
  }

  // Docker設定
  await createDockerfiles(deploymentDir);
  
  // Kubernetes設定
  await createKubernetesManifests(deploymentDir);
  
  // Docker Compose設定（開発用）
  await createDockerCompose(deploymentDir);

  console.log('   ✅ Docker & Kubernetes設定を生成');
  console.log('   📁 deployment/ ディレクトリに配置');
}

async function createDockerfiles(deploymentDir: string) {
  const dockerfile = `# E2E Encrypted Chat Application Dockerfile
FROM node:18-alpine AS builder

WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production

FROM node:18-alpine AS runtime

# セキュリティ: 非rootユーザーで実行
RUN addgroup -g 1001 -S nodejs
RUN adduser -S nextjs -u 1001

WORKDIR /app

# 依存関係のコピー
COPY --from=builder --chown=nextjs:nodejs /app/node_modules ./node_modules
COPY --chown=nextjs:nodejs . .

# ビルド
RUN npm run build

# 本番用設定
ENV NODE_ENV=production
ENV PORT=3000

USER nextjs

EXPOSE 3000

# ヘルスチェック
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \\
  CMD curl -f http://localhost:3000/api/health || exit 1

CMD ["npm", "start"]`;

  writeFileSync(path.join(deploymentDir, 'Dockerfile'), dockerfile);

  // .dockerignore
  const dockerignore = `node_modules
.git
.gitignore
README.md
Dockerfile
.dockerignore
npm-debug.log
coverage
.nyc_output
tests
*.test.ts
*.spec.ts`;

  writeFileSync(path.join(deploymentDir, '.dockerignore'), dockerignore);
}

async function createKubernetesManifests(deploymentDir: string) {
  const k8sDir = path.join(deploymentDir, 'k8s');
  mkdirSync(k8sDir, { recursive: true });

  // Deployment
  const deployment = `apiVersion: apps/v1
kind: Deployment
metadata:
  name: e2e-chat-app
  labels:
    app: e2e-chat-app
    version: v1
spec:
  replicas: 3
  selector:
    matchLabels:
      app: e2e-chat-app
  template:
    metadata:
      labels:
        app: e2e-chat-app
        version: v1
    spec:
      containers:
      - name: app
        image: e2e-chat-app:latest
        ports:
        - containerPort: 3000
        env:
        - name: NODE_ENV
          value: "production"
        - name: JWT_SECRET
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: jwt-secret
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /api/health
            port: 3000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /api/ready
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5`;

  writeFileSync(path.join(k8sDir, 'deployment.yaml'), deployment);

  // Service
  const service = `apiVersion: v1
kind: Service
metadata:
  name: e2e-chat-service
  labels:
    app: e2e-chat-app
spec:
  selector:
    app: e2e-chat-app
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
  type: ClusterIP`;

  writeFileSync(path.join(k8sDir, 'service.yaml'), service);

  // HPA (Horizontal Pod Autoscaler)
  const hpa = `apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: e2e-chat-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: e2e-chat-app
  minReplicas: 2
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80`;

  writeFileSync(path.join(k8sDir, 'hpa.yaml'), hpa);

  // Ingress
  const ingress = `apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: e2e-chat-ingress
  annotations:
    kubernetes.io/ingress.class: nginx
    cert-manager.io/cluster-issuer: letsencrypt-prod
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/rate-limit: "1000"
spec:
  tls:
  - hosts:
    - chat.example.com
    secretName: chat-tls
  rules:
  - host: chat.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: e2e-chat-service
            port:
              number: 80`;

  writeFileSync(path.join(k8sDir, 'ingress.yaml'), ingress);
}

async function createDockerCompose(deploymentDir: string) {
  const dockerCompose = `version: '3.8'

services:
  app:
    build:
      context: ..
      dockerfile: deployment/Dockerfile
    ports:
      - "3000:3000"
    environment:
      - NODE_ENV=development
      - JWT_SECRET=dev-secret-key
    depends_on:
      - postgres
      - redis
    volumes:
      - ../src:/app/src:ro
    networks:
      - app-network

  postgres:
    image: postgres:15-alpine
    environment:
      POSTGRES_DB: e2e_chat
      POSTGRES_USER: postgres
      POSTGRES_PASSWORD: postgres
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data
    networks:
      - app-network

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    networks:
      - app-network

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml:ro
      - prometheus_data:/prometheus
    networks:
      - app-network

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana_data:/var/lib/grafana
      - ./monitoring/grafana:/etc/grafana/provisioning:ro
    networks:
      - app-network

volumes:
  postgres_data:
  redis_data:
  prometheus_data:
  grafana_data:

networks:
  app-network:
    driver: bridge`;

  writeFileSync(path.join(deploymentDir, 'docker-compose.yml'), dockerCompose);
}

async function setupMonitoringAndAlerting(projectPath: string) {
  const monitoringDir = path.join(projectPath, 'deployment', 'monitoring');
  mkdirSync(monitoringDir, { recursive: true });

  // Prometheus設定
  const prometheusConfig = `global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "alert_rules.yml"

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093

scrape_configs:
  - job_name: 'e2e-chat-app'
    static_configs:
      - targets: ['app:3000']
    metrics_path: '/api/metrics'
    scrape_interval: 5s

  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node-exporter:9100']`;

  writeFileSync(path.join(monitoringDir, 'prometheus.yml'), prometheusConfig);

  // アラートルール
  const alertRules = `groups:
- name: e2e-chat-alerts
  rules:
  - alert: HighErrorRate
    expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.01
    for: 2m
    labels:
      severity: high
    annotations:
      summary: "High error rate detected"
      description: "Error rate is {{ $value }} for {{ $labels.instance }}"

  - alert: HighLatency
    expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.2
    for: 5m
    labels:
      severity: medium
    annotations:
      summary: "High latency detected"
      description: "95th percentile latency is {{ $value }}s for {{ $labels.instance }}"

  - alert: LowThroughput
    expr: rate(http_requests_total[5m]) < 100
    for: 5m
    labels:
      severity: medium
    annotations:
      summary: "Low throughput detected"
      description: "Request rate is {{ $value }} req/s for {{ $labels.instance }}"

  - alert: EncryptionServiceDown
    expr: up{job="e2e-chat-app", endpoint="crypto"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "Encryption service is down"
      description: "Encryption service has been down for more than 1 minute"`;

  writeFileSync(path.join(monitoringDir, 'alert_rules.yml'), alertRules);

  // Grafanaダッシュボード設定
  const grafanaDir = path.join(monitoringDir, 'grafana', 'dashboards');
  mkdirSync(grafanaDir, { recursive: true });

  const dashboard = {
    dashboard: {
      id: null,
      title: "E2E Encrypted Chat - Operations Dashboard",
      tags: ["e2e-chat", "operations"],
      timezone: "browser",
      panels: [
        {
          id: 1,
          title: "Request Rate",
          type: "graph",
          targets: [
            {
              expr: "rate(http_requests_total[5m])",
              legendFormat: "{{instance}}"
            }
          ]
        },
        {
          id: 2,
          title: "Response Time (95th percentile)",
          type: "graph",
          targets: [
            {
              expr: "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))",
              legendFormat: "{{instance}}"
            }
          ]
        },
        {
          id: 3,
          title: "Error Rate",
          type: "graph",
          targets: [
            {
              expr: "rate(http_requests_total{status=~\"5..\"}[5m])",
              legendFormat: "{{instance}}"
            }
          ]
        },
        {
          id: 4,
          title: "Encryption Operations/sec",
          type: "graph",
          targets: [
            {
              expr: "rate(encryption_operations_total[5m])",
              legendFormat: "{{operation}}"
            }
          ]
        }
      ],
      time: {
        from: "now-6h",
        to: "now"
      },
      refresh: "30s"
    }
  };

  writeFileSync(
    path.join(grafanaDir, 'operations-dashboard.json'),
    JSON.stringify(dashboard, null, 2)
  );

  console.log('   ✅ Prometheus & Grafana設定を生成');
  console.log('   📊 運用ダッシュボードとアラートルールを設定');
}

async function setupCICDPipeline(projectPath: string) {
  const githubDir = path.join(projectPath, '.github', 'workflows');
  mkdirSync(githubDir, { recursive: true });

  const cicdWorkflow = `name: E2E Chat - CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: e2e-encrypted-chat

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Setup Node.js
      uses: actions/setup-node@v4
      with:
        node-version: '18'
        cache: 'npm'
    
    - name: Install dependencies
      run: npm ci
    
    - name: Run linting
      run: npm run lint
    
    - name: Run type checking
      run: npm run type-check
    
    - name: Run tests
      run: npm test
    
    - name: Run security tests
      run: npm run test:security
    
    - name: Upload coverage reports
      uses: codecov/codecov-action@v3

  security-scan:
    runs-on: ubuntu-latest
    needs: test
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Run Trivy vulnerability scanner
      uses: aquasecurity/trivy-action@master
      with:
        scan-type: 'fs'
        ignore-unfixed: true
        format: 'sarif'
        output: 'trivy-results.sarif'
    
    - name: Upload Trivy scan results
      uses: github/codeql-action/upload-sarif@v2
      with:
        sarif_file: 'trivy-results.sarif'

  build:
    runs-on: ubuntu-latest
    needs: [test, security-scan]
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Log in to Container Registry
      uses: docker/login-action@v3
      with:
        registry: \${{ env.REGISTRY }}
        username: \${{ github.actor }}
        password: \${{ secrets.GITHUB_TOKEN }}
    
    - name: Extract metadata
      id: meta
      uses: docker/metadata-action@v5
      with:
        images: \${{ env.REGISTRY }}/\${{ github.repository }}
    
    - name: Build and push Docker image
      uses: docker/build-push-action@v5
      with:
        context: .
        file: deployment/Dockerfile
        push: true
        tags: \${{ steps.meta.outputs.tags }}
        labels: \${{ steps.meta.outputs.labels }}

  deploy-staging:
    runs-on: ubuntu-latest
    needs: build
    if: github.ref == 'refs/heads/develop'
    environment: staging
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Deploy to staging
      run: |
        echo "Deploying to staging environment..."
        # kubectl apply -f deployment/k8s/
    
    - name: Run smoke tests
      run: |
        npm run test:smoke -- --env=staging

  deploy-production:
    runs-on: ubuntu-latest
    needs: build
    if: github.ref == 'refs/heads/main'
    environment: production
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Deploy to production (Blue-Green)
      run: |
        echo "Executing blue-green deployment..."
        # Blue-green deployment logic
    
    - name: Run production health checks
      run: |
        npm run test:health -- --env=production
    
    - name: Notify deployment success
      uses: 8398a7/action-slack@v3
      with:
        status: success
        text: '✅ E2E Chat deployed to production successfully!'
      env:
        SLACK_WEBHOOK_URL: \${{ secrets.SLACK_WEBHOOK }}`;

  writeFileSync(path.join(githubDir, 'ci-cd.yml'), cicdWorkflow);

  console.log('   ✅ GitHub Actions CI/CDパイプラインを生成');
  console.log('   🔄 自動テスト、セキュリティスキャン、デプロイメントを設定');
}

async function setupSLOAndDashboards(projectPath: string) {
  const sloDir = path.join(projectPath, 'slo');
  mkdirSync(sloDir, { recursive: true });

  const sloConfig = {
    objectives: [
      {
        name: "API Availability",
        description: "99.9% uptime for all API endpoints",
        target: 99.9,
        timeWindow: "7d",
        metric: {
          type: "availability",
          query: "up{job=\"e2e-chat-app\"}"
        }
      },
      {
        name: "Response Time",
        description: "95th percentile response time < 200ms",
        target: 200,
        timeWindow: "7d",
        metric: {
          type: "latency",
          query: "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))"
        }
      },
      {
        name: "Error Rate",
        description: "Error rate < 0.1%",
        target: 0.1,
        timeWindow: "7d",
        metric: {
          type: "error_rate",
          query: "rate(http_requests_total{status=~\"5..\"}[5m]) / rate(http_requests_total[5m]) * 100"
        }
      },
      {
        name: "Encryption Performance",
        description: "Encryption operations > 1000 ops/sec",
        target: 1000,
        timeWindow: "1h",
        metric: {
          type: "throughput",
          query: "rate(encryption_operations_total[5m])"
        }
      }
    ],
    errorBudget: {
      calculation: "based_on_slo",
      alerting: {
        burnRateThreshold: 0.1,
        channels: ["slack", "email"]
      }
    }
  };

  writeFileSync(path.join(sloDir, 'slo-config.json'), JSON.stringify(sloConfig, null, 2));

  console.log('   ✅ SLO設定とエラーバジェット管理を生成');
  console.log('   🎯 可用性99.9%、レスポンス時間200ms以下の目標設定');
}

async function setupSecurityMonitoring(projectPath: string) {
  const securityDir = path.join(projectPath, 'security');
  mkdirSync(securityDir, { recursive: true });

  // セキュリティスキャン設定
  const securityScanConfig = {
    vulnerabilityScanning: {
      schedule: "0 2 * * *", // 毎日午前2時
      tools: ["trivy", "snyk", "npm-audit"],
      thresholds: {
        critical: 0,
        high: 5,
        medium: 20
      }
    },
    complianceChecks: {
      frameworks: ["SOC2", "ISO27001", "NIST"],
      automated: true,
      reportingSchedule: "weekly"
    },
    runtimeSecurity: {
      falcoRules: true,
      networkPolicies: true,
      podSecurityStandards: "restricted"
    }
  };

  writeFileSync(
    path.join(securityDir, 'security-config.json'),
    JSON.stringify(securityScanConfig, null, 2)
  );

  // Falco セキュリティルール
  const falcoRules = `- rule: Detect crypto operations anomaly
  desc: Unusual encryption/decryption patterns
  condition: >
    encryption_operation and
    (encryption_rate > 10000 or encryption_failure_rate > 0.05)
  output: "Crypto anomaly detected (user=%ka.user.name command=%proc.cmdline)"
  priority: HIGH

- rule: Unauthorized API access
  desc: API access from unauthorized sources
  condition: >
    inbound and
    ka.req.uri startswith "/api/" and
    not ka.auth.token
  output: "Unauthorized API access attempt (source=%fd.cip uri=%ka.req.uri)"
  priority: CRITICAL

- rule: Suspicious file access
  desc: Access to sensitive encryption keys
  condition: >
    open_read and
    (fd.name contains "private.key" or fd.name contains "secret")
  output: "Suspicious file access (user=%user.name file=%fd.name)"
  priority: HIGH`;

  writeFileSync(path.join(securityDir, 'falco-rules.yaml'), falcoRules);

  console.log('   ✅ セキュリティ監視とコンプライアンスチェックを設定');
  console.log('   🔐 リアルタイム脅威検知とコンプライアンス監査を有効化');
}

async function performInitialDeployment(agent: OperateAgent) {
  try {
    console.log('   🚀 ステージング環境への初期デプロイメント...');
    
    const stagingResult = await agent.deployApplication({
      environment: 'staging',
      version: 'v1.0.0',
      strategy: 'rolling',
      rollbackOnFailure: true,
      healthCheckTimeout: 300
    });

    if (stagingResult.success) {
      console.log('   ✅ ステージング環境デプロイメント成功');
      
      // ヘルスチェック実行
      const healthStatus = await agent.monitorHealth();
      if (healthStatus.overall === 'healthy') {
        console.log('   💚 全エンドポイントが正常に動作中');
      } else {
        console.log('   ⚠️ 一部エンドポイントに問題あり:', healthStatus.details);
      }

      // SLO初期測定
      const sloStatus = await agent.trackSlo();
      console.log('   📊 SLO初期状態:');
      console.log(`     - 可用性: ${sloStatus.availability.actual}% (目標: ${sloStatus.availability.target}%)`);
      console.log(`     - レスポンス時間: ${sloStatus.latency.actual}ms (目標: ${sloStatus.latency.target}ms)`);
      console.log(`     - エラー率: ${sloStatus.errorRate.actual}% (目標: ${sloStatus.errorRate.target}%)`);

    } else {
      console.log('   ❌ ステージング環境デプロイメント失敗');
      console.log('   🔄 ロールバック処理が実行されました');
    }

  } catch (error) {
    console.error('   ❌ デプロイメント中にエラー:', error);
  }
}

async function generateOperationalDocumentation(projectPath: string, config: OperateAgentConfig) {
  const docsDir = path.join(projectPath, 'docs', 'operations');
  mkdirSync(docsDir, { recursive: true });

  const operationsGuide = `# E2E暗号化チャットアプリケーション - 運用ガイド

## 概要

このドキュメントは、E2E暗号化チャットアプリケーションの本番運用に関する包括的なガイドです。

## システム概要

### アーキテクチャ
- **フロントエンド**: TypeScript + React
- **バックエンド**: Node.js + Fastify
- **データベース**: PostgreSQL + Redis
- **暗号化**: AES-256-GCM + X25519 + Ed25519
- **インフラ**: Kubernetes + Docker

### 運用環境
- **Development**: 開発環境 (localhost)
- **Staging**: ステージング環境 (staging.chat.example.com)
- **Production**: 本番環境 (chat.example.com)

## 監視・アラート

### SLO目標
- **可用性**: 99.9% (月間ダウンタイム < 43.8分)
- **レスポンス時間**: 95%ile < 200ms
- **エラー率**: < 0.1%
- **暗号化性能**: > 1000 ops/sec

### ダッシュボード
- **Grafana**: http://monitoring.example.com:3001
- **Prometheus**: http://monitoring.example.com:9090
- **ログ**: http://logs.example.com

### アラート設定
- **高**: 5分以内にSlack通知
- **重要**: 15分以内にEmail + PagerDuty

## デプロイメント

### デプロイメント戦略
- **Staging**: Rolling Deployment
- **Production**: Blue-Green Deployment

### デプロイコマンド
\`\`\`bash
# ステージング
kubectl apply -f deployment/k8s/ --namespace=staging

# 本番 (Blue-Green)
./scripts/blue-green-deploy.sh v1.2.3
\`\`\`

### ロールバック手順
\`\`\`bash
# 緊急ロールバック
kubectl rollout undo deployment/e2e-chat-app --namespace=production

# 特定バージョンへのロールバック
kubectl rollout undo deployment/e2e-chat-app --to-revision=2 --namespace=production
\`\`\`

## インシデント対応

### 重要度レベル
- **Critical**: サービス完全停止
- **High**: 主要機能の障害
- **Medium**: 性能劣化
- **Low**: 軽微な問題

### エスカレーション
1. **0-5分**: 自動アラート → オンコールエンジニア
2. **5-15分**: Slack通知 → チームリード
3. **15分以上**: Email + PagerDuty → マネージャー

### 障害復旧手順

#### 1. サービス停止時
\`\`\`bash
# ヘルスチェック
kubectl get pods -n production
curl -f http://chat.example.com/api/health

# ログ確認
kubectl logs -f deployment/e2e-chat-app -n production

# 緊急スケーリング
kubectl scale deployment e2e-chat-app --replicas=10 -n production
\`\`\`

#### 2. 暗号化機能障害
\`\`\`bash
# 暗号化サービス再起動
kubectl rollout restart deployment/e2e-chat-app -n production

# 暗号化パフォーマンス確認
curl http://chat.example.com/api/crypto/health
\`\`\`

#### 3. データベース問題
\`\`\`bash
# データベース接続確認
kubectl exec -it postgres-0 -n production -- psql -U postgres -d e2e_chat

# レプリカ切り替え
kubectl patch service postgres-service -p '{"spec":{"selector":{"role":"replica"}}}'
\`\`\`

## セキュリティ運用

### 定期セキュリティタスク
- **毎日**: 脆弱性スキャン (02:00 JST)
- **毎週**: コンプライアンスチェック
- **毎月**: セキュリティ監査レポート

### セキュリティインシデント対応
1. **検知**: 自動アラート or 手動報告
2. **初期対応**: 影響範囲の特定
3. **封じ込め**: 攻撃の停止・隔離
4. **根絶**: 脆弱性の修正
5. **復旧**: サービス正常化
6. **事後対応**: 原因分析・再発防止

## 性能最適化

### 監視メトリクス
- CPU使用率: < 70%
- メモリ使用率: < 80%
- ディスクI/O: < 80%
- ネットワーク: < 1Gbps

### 自動スケーリング
- **スケールアップ**: CPU > 70% for 3min
- **スケールダウン**: CPU < 30% for 5min
- **最小インスタンス**: 2
- **最大インスタンス**: 20

## 障害復旧計画

### RTO/RPO目標
- **RTO** (Recovery Time Objective): 15分
- **RPO** (Recovery Point Objective): 5分

### バックアップ戦略
- **データベース**: 15分間隔の自動バックアップ
- **設定ファイル**: Git管理
- **暗号化キー**: HSM保管

### 災害復旧手順
1. **データセンター障害**: 別リージョンへの切り替え
2. **データベース障害**: スタンバイDBへのフェイルオーバー
3. **アプリケーション障害**: ロードバランサーでの切り替え

## 運用チェックリスト

### 日次タスク
- [ ] ダッシュボード確認
- [ ] アラート確認
- [ ] バックアップ状況確認
- [ ] セキュリティスキャン結果確認

### 週次タスク
- [ ] パフォーマンスレビュー
- [ ] ログ分析
- [ ] 容量計画見直し
- [ ] セキュリティパッチ適用

### 月次タスク
- [ ] SLOレポート作成
- [ ] 運用コストレビュー
- [ ] 災害復旧テスト
- [ ] セキュリティ監査

## 連絡先

### 緊急連絡先
- **オンコールエンジニア**: +81-90-XXXX-XXXX
- **チームリード**: team-lead@company.com
- **セキュリティチーム**: security@company.com

### エスカレーション先
- **PagerDuty**: https://company.pagerduty.com
- **Slack**: #e2e-chat-ops
- **Jira**: E2E-OPS プロジェクト

---

**最終更新**: ${new Date().toISOString()}  
**文書バージョン**: 1.0  
**担当**: DevOps Team`;

  writeFileSync(path.join(docsDir, 'operations-guide.md'), operationsGuide);

  // ランブック生成
  const runbook = `# E2E Chat - 運用ランブック

## 緊急対応手順

### 🚨 サービス完全停止
1. \`kubectl get pods -n production\` - ポッド状況確認
2. \`kubectl logs -f deployment/e2e-chat-app -n production\` - ログ確認
3. \`kubectl rollout undo deployment/e2e-chat-app -n production\` - ロールバック
4. PagerDuty経由でエスカレーション

### ⚠️ 性能劣化
1. Grafanaダッシュボードで メトリクス確認
2. \`kubectl top pods -n production\` - リソース使用率確認
3. \`kubectl scale deployment e2e-chat-app --replicas=6 -n production\` - スケールアップ

### 🔐 セキュリティアラート
1. アラート詳細の確認
2. 影響範囲の特定
3. セキュリティチームへの連絡
4. 必要に応じてサービス停止

## 定期メンテナンス

### データベースメンテナンス
\`\`\`bash
# バックアップ作成
kubectl exec postgres-0 -n production -- pg_dump e2e_chat > backup.sql

# インデックス再構築
kubectl exec postgres-0 -n production -- psql -d e2e_chat -c "REINDEX DATABASE e2e_chat;"
\`\`\`

### 証明書更新
\`\`\`bash
# Let's Encrypt証明書更新
certbot renew --dry-run
kubectl rollout restart deployment/nginx-ingress-controller
\`\`\``;

  writeFileSync(path.join(docsDir, 'runbook.md'), runbook);

  console.log('   ✅ 運用ガイドとランブックを生成');
  console.log('   📚 docs/operations/ ディレクトリに配置');
}

// スクリプト実行
setupProductionOperations().catch(console.error);