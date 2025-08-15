import { initTelemetry } from './infra/telemetry';
import { Database, initDatabase } from './infra/db';
import app from './api/server';

async function start() {
  // Initialize telemetry
  initTelemetry();

  // Initialize database
  const db = new Database(
    process.env.DATABASE_URL || 'postgresql://app:app@localhost:5432/e2echat'
  );
  
  // Run migrations
  await initDatabase(db);

  // Start server
  const port = process.env.PORT ? parseInt(process.env.PORT) : 3000;
  const host = process.env.HOST || '0.0.0.0';

  try {
    await app.listen({ port, host });
    console.log(`🔐 E2E Encrypted Chat Server`);
    console.log(`📡 HTTP Server: http://${host}:${port}`);
    console.log(`🔌 WebSocket: ws://${host}:${port}/ws`);
    console.log(`📚 API Docs: http://${host}:${port}/docs`);
    console.log(`🏥 Health: http://${host}:${port}/health`);
  } catch (err) {
    app.log.error(err);
    process.exit(1);
  }
}

start().catch(console.error);