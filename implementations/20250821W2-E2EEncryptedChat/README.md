# E2E Encrypted Chat Application

End-to-End encrypted chat application built with AE-Framework implementing the Signal Protocol.

## Features

- 🔒 **End-to-End Encryption**: Messages are encrypted on the sender's device and can only be decrypted by the intended recipient
- 🔑 **Perfect Forward Secrecy**: Uses Double Ratchet algorithm ensuring past messages remain secure even if keys are compromised
- ✅ **Security Number Verification**: Verify chat sessions through QR codes or security numbers
- 🚀 **Real-time Messaging**: WebSocket-based real-time message delivery
- 🔄 **Multi-device Support**: Sync messages across multiple devices securely
- 📱 **Typing Indicators & Read Receipts**: Real-time presence and activity updates

## Architecture

```
┌─────────────┐     ┌──────────────┐     ┌─────────────┐
│   Client A  │────▶│   Server     │◀────│   Client B  │
│  (Browser)  │     │  (Relay Only)│     │  (Browser)  │
└─────────────┘     └──────────────┘     └─────────────┘
      │                    │                    │
      │   Encrypted        │                    │
      │   Message          │  Cannot Read       │
      └────────────────────┴────────────────────┘
                    E2E Encrypted
```

## Tech Stack

- **Encryption**: Signal Protocol (X3DH + Double Ratchet)
- **Backend**: Node.js, Express, WebSocket
- **Crypto**: Noble/ed25519, TweetNaCl
- **Storage**: In-memory (demo) / PostgreSQL (production)
- **Framework**: AE-Framework for specification-driven development

## Installation

```bash
# Install dependencies
npm install

# Build the application
npm run build

# Run tests
npm test
```

## Usage

### Starting the Server

```bash
# Start both REST API and WebSocket server
npm start

# Development mode with hot reload
npm run dev
```

The application will start:
- REST API on http://localhost:3000
- WebSocket server on ws://localhost:8080

### API Endpoints

#### Authentication
```bash
# Register new user
POST /api/auth/register
{
  "email": "user@example.com",
  "displayName": "Alice",
  "password": "securepassword"
}

# Login
POST /api/auth/login
{
  "email": "user@example.com",
  "password": "securepassword"
}
```

#### Chat Sessions
```bash
# Create new chat session
POST /api/sessions
{
  "userId": "user-id",
  "recipientId": "recipient-id"
}

# Get messages
GET /api/sessions/{sessionId}/messages

# Verify session
POST /api/sessions/{sessionId}/verify
{
  "userId": "user-id",
  "securityNumber": "12345 67890 ..."
}
```

### WebSocket Client Example

```javascript
// Connect to WebSocket
const ws = new WebSocket('ws://localhost:8080/ws');

// Authenticate
ws.send(JSON.stringify({
  type: 'auth',
  payload: {
    userId: 'user-id',
    token: 'auth-token'
  },
  id: 'msg-1'
}));

// Send encrypted message
ws.send(JSON.stringify({
  type: 'message',
  payload: {
    sessionId: 'session-id',
    message: encryptedMessage
  },
  id: 'msg-2'
}));
```

## Security Implementation

### Encryption Flow

1. **Key Generation**: Each user generates:
   - Identity Key Pair (long-term)
   - Signed Pre-Key (medium-term, signed by identity key)
   - One-Time Pre-Keys (ephemeral, consumed per session)

2. **Session Establishment** (X3DH):
   - Alice fetches Bob's key bundle
   - Performs triple Diffie-Hellman key exchange
   - Derives shared secret for Double Ratchet initialization

3. **Message Encryption** (Double Ratchet):
   - Derives unique message key for each message
   - Provides forward secrecy through key ratcheting
   - Handles out-of-order message delivery

### Security Features

- **Zero-Knowledge Architecture**: Server never has access to plaintext messages
- **Perfect Forward Secrecy**: Compromised keys don't affect past messages
- **Future Secrecy**: Compromised keys automatically heal with continued communication
- **Deniable Authentication**: Messages are authenticated but repudiable

## Testing

```bash
# Run all tests
npm test

# Run encryption tests
npm test -- encryption.test.ts

# Run with coverage
npm test -- --coverage
```

## Development

### Project Structure

```
e2e-chat/
├── src/
│   ├── crypto/          # Encryption modules
│   │   ├── encryption.ts
│   │   └── double-ratchet.ts
│   ├── domain/          # Domain entities
│   │   └── entities.ts
│   ├── services/        # Business logic
│   │   └── chat-service.ts
│   ├── server/          # WebSocket server
│   │   └── websocket-server.ts
│   ├── client/          # Client implementation
│   │   └── chat-client.ts
│   ├── repository/      # Data persistence
│   │   └── in-memory-repository.ts
│   └── index.ts         # Main entry point
├── tests/               # Test files
├── specs/               # AE-Framework specifications
└── package.json
```

### Adding Features

1. Create specification in `specs/` using AE-Framework format
2. Compile specification: `npm run compile-spec`
3. Implement feature following TDD approach
4. Add tests in `tests/`
5. Update documentation

## Production Considerations

### Database
- Replace in-memory repository with PostgreSQL/MongoDB
- Implement proper message persistence and indexing
- Add backup and recovery mechanisms

### Scaling
- Use Redis for session management
- Implement horizontal scaling for WebSocket servers
- Add load balancing with sticky sessions

### Security Hardening
- Implement rate limiting
- Add DDoS protection
- Enable CORS with specific origins
- Use HTTPS/WSS in production
- Implement proper authentication (OAuth2/JWT)
- Add security headers (CSP, HSTS, etc.)

### Monitoring
- Add OpenTelemetry instrumentation
- Implement health checks
- Set up alerting for security events
- Monitor key rotation and usage

## License

MIT

## Contributing

Please read CONTRIBUTING.md for details on our code of conduct and the process for submitting pull requests.

## Acknowledgments

- Signal Protocol specification
- AE-Framework for specification-driven development
- Noble cryptography libraries