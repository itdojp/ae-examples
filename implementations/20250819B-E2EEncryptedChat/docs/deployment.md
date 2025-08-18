# E2E Encrypted Chat - Deployment Guide

## Prerequisites

- Docker 20.10+
- Kubernetes 1.25+ (for production)
- Node.js 18+
- PostgreSQL 14+
- Redis 7+

## Environment Setup

### Development Environment

1. **Clone the repository**
```bash
git clone https://github.com/itdojp/ae-examples.git
cd ae-examples/20250819B-E2EEncryptedChat
```

2. **Install dependencies**
```bash
npm install
```

3. **Set up environment variables**
```bash
cp .env.example .env.development
# Edit .env.development with your values
```

4. **Start development services**
```bash
docker-compose -f docker-compose.dev.yml up -d
npm run dev
```

### Staging Environment

1. **Build Docker images**
```bash
docker build -t e2e-chat-api:staging -f Dockerfile.api .
docker build -t e2e-chat-web:staging -f Dockerfile.web .
```

2. **Deploy to Kubernetes**
```bash
kubectl apply -f k8s/staging/
```

3. **Configure ingress**
```bash
kubectl apply -f k8s/staging/ingress.yaml
```

### Production Environment

1. **Production build**
```bash
npm run build:production
```

2. **Docker images with tags**
```bash
docker build -t e2e-chat-api:v1.0.0 -f Dockerfile.api .
docker build -t e2e-chat-web:v1.0.0 -f Dockerfile.web .
```

3. **Push to registry**
```bash
docker push your-registry/e2e-chat-api:v1.0.0
docker push your-registry/e2e-chat-web:v1.0.0
```

4. **Deploy with Helm**
```bash
helm install e2e-chat ./helm-chart \
  --values ./helm-chart/values.production.yaml \
  --namespace production
```

## Configuration

### Database Setup

```sql
-- Create database
CREATE DATABASE e2e_chat_production;

-- Create user
CREATE USER e2e_chat_user WITH PASSWORD 'secure_password';

-- Grant privileges
GRANT ALL PRIVILEGES ON DATABASE e2e_chat_production TO e2e_chat_user;
```

### Redis Configuration

```bash
# redis.conf
maxmemory 2gb
maxmemory-policy allkeys-lru
save 900 1
save 300 10
save 60 10000
```

### Environment Variables

```env
# Application
NODE_ENV=production
PORT=3000
API_URL=https://api.e2echat.com

# Database
DATABASE_URL=postgresql://user:password@host:5432/e2e_chat
DATABASE_POOL_SIZE=20

# Redis
REDIS_URL=redis://redis:6379
REDIS_PASSWORD=redis_password

# Security
JWT_SECRET=your-jwt-secret
ENCRYPTION_KEY=your-encryption-key

# WebSocket
WS_PORT=3001
WS_CORS_ORIGIN=https://e2echat.com

# Monitoring
OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4318
OTEL_SERVICE_NAME=e2e-chat

# Features
ENABLE_E2E_ENCRYPTION=true
ENABLE_MULTI_DEVICE=true
ENABLE_GROUP_CHAT=false
```

## Deployment Checklist

### Pre-deployment

- [ ] All tests passing
- [ ] Security audit completed
- [ ] Performance benchmarks met
- [ ] Documentation updated
- [ ] Environment variables configured
- [ ] SSL certificates ready
- [ ] Database migrations prepared
- [ ] Backup strategy implemented

### Deployment Steps

1. **Database Migration**
```bash
npm run migrate:production
```

2. **Deploy Backend Services**
```bash
kubectl rollout status deployment/e2e-chat-api
```

3. **Deploy Frontend**
```bash
kubectl rollout status deployment/e2e-chat-web
```

4. **Verify Health Checks**
```bash
curl https://api.e2echat.com/health
```

5. **Run Smoke Tests**
```bash
npm run test:smoke
```

### Post-deployment

- [ ] Monitor error rates
- [ ] Check performance metrics
- [ ] Verify security headers
- [ ] Test critical user flows
- [ ] Monitor resource usage
- [ ] Check backup completion
- [ ] Update status page

## Rollback Procedure

```bash
# Rollback to previous version
kubectl rollout undo deployment/e2e-chat-api
kubectl rollout undo deployment/e2e-chat-web

# Verify rollback
kubectl rollout status deployment/e2e-chat-api
kubectl rollout status deployment/e2e-chat-web
```

## Monitoring

### Health Endpoints

- API Health: `GET /health`
- WebSocket Health: `GET /ws/health`
- Database Health: `GET /health/db`
- Redis Health: `GET /health/redis`

### Metrics to Monitor

- Request latency (p50, p95, p99)
- Error rate
- Active connections
- Message throughput
- Database connection pool
- Redis memory usage
- CPU and memory utilization

### Alerts

```yaml
# Example Prometheus alert
- alert: HighErrorRate
  expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.05
  for: 5m
  annotations:
    summary: "High error rate detected"
    
- alert: HighLatency
  expr: histogram_quantile(0.95, http_request_duration_seconds) > 0.5
  for: 10m
  annotations:
    summary: "High latency detected"
```

## Scaling

### Horizontal Scaling

```bash
# Scale API servers
kubectl scale deployment e2e-chat-api --replicas=5

# Scale WebSocket servers
kubectl scale deployment e2e-chat-ws --replicas=3
```

### Auto-scaling

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: e2e-chat-api-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: e2e-chat-api
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
```

## Security Considerations

### SSL/TLS Configuration

```nginx
# nginx.conf
ssl_protocols TLSv1.2 TLSv1.3;
ssl_ciphers HIGH:!aNULL:!MD5;
ssl_prefer_server_ciphers on;
ssl_session_cache shared:SSL:10m;
ssl_session_timeout 10m;
```

### Security Headers

```nginx
add_header Strict-Transport-Security "max-age=31536000; includeSubDomains" always;
add_header X-Frame-Options "DENY" always;
add_header X-Content-Type-Options "nosniff" always;
add_header X-XSS-Protection "1; mode=block" always;
add_header Content-Security-Policy "default-src 'self'" always;
```

## Troubleshooting

### Common Issues

1. **Database Connection Issues**
   - Check connection string
   - Verify network connectivity
   - Check connection pool settings

2. **WebSocket Connection Failures**
   - Verify CORS settings
   - Check firewall rules
   - Ensure sticky sessions enabled

3. **High Memory Usage**
   - Review Redis eviction policy
   - Check for memory leaks
   - Optimize message batching

### Debug Commands

```bash
# Check pod logs
kubectl logs -f deployment/e2e-chat-api

# Execute commands in pod
kubectl exec -it deployment/e2e-chat-api -- /bin/bash

# Check resource usage
kubectl top pods

# Describe deployment
kubectl describe deployment e2e-chat-api
```

## Support

For deployment support:
- Documentation: [Wiki](https://github.com/itdojp/ae-examples/wiki)
- Issues: [GitHub Issues](https://github.com/itdojp/ae-examples/issues)
- Email: support@e2echat.example.com