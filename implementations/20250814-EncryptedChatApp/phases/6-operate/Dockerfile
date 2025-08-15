# E2E暗号化チャットアプリケーション - Production Dockerfile
# Multi-stage build for optimal image size and security

# Stage 1: Build WebUI
FROM node:18-alpine AS webui-builder

WORKDIR /app/webui

# Copy WebUI package files
COPY phases/4-code/webui/package*.json ./
RUN npm ci --only=production

# Copy WebUI source code
COPY phases/4-code/webui/ ./

# Build production WebUI
RUN npm run build

# Stage 2: Build Backend
FROM node:18-alpine AS backend-builder

WORKDIR /app/backend

# Copy backend package files
COPY phases/4-code/backend/package*.json ./
RUN npm ci --only=production

# Copy backend source code
COPY phases/4-code/backend/ ./

# Stage 3: Production Runtime
FROM node:18-alpine AS production

# Security: Create non-root user
RUN addgroup -g 1001 -S chatapp && \
    adduser -S chatapp -u 1001

# Install security updates
RUN apk update && apk upgrade && \
    apk add --no-cache \
    ca-certificates \
    tzdata && \
    rm -rf /var/cache/apk/*

# Set timezone
ENV TZ=Asia/Tokyo

WORKDIR /app

# Copy backend from builder
COPY --from=backend-builder --chown=chatapp:chatapp /app/backend ./backend

# Copy built WebUI
COPY --from=webui-builder --chown=chatapp:chatapp /app/webui/dist ./webui/dist

# Copy static files and configs
COPY --chown=chatapp:chatapp phases/6-operate/docker/nginx.conf ./nginx.conf
COPY --chown=chatapp:chatapp phases/6-operate/docker/start.sh ./start.sh
COPY --chown=chatapp:chatapp start.sh ./start-app.sh

# Install nginx for serving static files
RUN apk add --no-cache nginx && \
    mkdir -p /var/log/nginx /var/lib/nginx/tmp && \
    chown -R chatapp:chatapp /var/log/nginx /var/lib/nginx

# Set proper permissions
RUN chmod +x ./start.sh ./start-app.sh && \
    chown -R chatapp:chatapp /app

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD node backend/healthcheck.js || exit 1

# Switch to non-root user
USER chatapp

# Environment variables
ENV NODE_ENV=production
ENV PORT=3000
ENV WEBUI_PORT=4173
ENV JWT_SECRET_FILE=/run/secrets/jwt_secret
ENV DB_HOST=db
ENV DB_PORT=5432
ENV REDIS_HOST=redis
ENV REDIS_PORT=6379

# Expose ports
EXPOSE 3000 4173 80

# Labels for metadata
LABEL \
    org.opencontainers.image.title="E2E Encrypted Chat App" \
    org.opencontainers.image.description="End-to-end encrypted chat application with WebUI" \
    org.opencontainers.image.version="1.0.0" \
    org.opencontainers.image.created="2025-08-14" \
    org.opencontainers.image.authors="ae-framework" \
    org.opencontainers.image.source="https://github.com/itdojp/ae-examples" \
    org.opencontainers.image.vendor="ae-framework project"

# Start script
CMD ["./start.sh"]