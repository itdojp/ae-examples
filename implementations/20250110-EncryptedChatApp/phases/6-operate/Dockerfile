# Multi-stage build for E2E Encrypted Chat Application
FROM docker.io/node:22-alpine AS deps

# Install build dependencies
RUN apk add --no-cache python3 make g++ git libsodium-dev

WORKDIR /app
COPY package*.json ./
RUN npm ci

FROM deps AS build
COPY . .
RUN npm run build

# Production stage
FROM docker.io/node:22-alpine

# Install runtime dependencies
RUN apk add --no-cache \
    libsodium \
    postgresql-client \
    curl \
    && addgroup -g 1001 -S nodejs \
    && adduser -S nodejs -u 1001

WORKDIR /app

# Set environment variables
ENV NODE_ENV=production \
    LOG_LEVEL=info \
    PORT=3000 \
    HOST=0.0.0.0

# Copy built application and production dependencies
COPY --from=deps --chown=nodejs:nodejs /app/node_modules ./node_modules
COPY --from=build --chown=nodejs:nodejs /app/dist ./dist
COPY --chown=nodejs:nodejs package*.json ./
COPY --chown=nodejs:nodejs migrations ./migrations
COPY --chown=nodejs:nodejs policies ./policies
COPY --chown=nodejs:nodejs specs ./specs

# Create necessary directories
RUN mkdir -p /app/logs /app/tmp && \
    chown -R nodejs:nodejs /app/logs /app/tmp

# Switch to non-root user
USER nodejs

# Expose ports
EXPOSE 3000
EXPOSE 9464

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:3000/health || exit 1

# Start the application
CMD ["node","dist/index.js"]