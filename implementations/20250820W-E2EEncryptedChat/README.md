# E2E Encrypted Chat Application

An end-to-end encrypted chat application built with the ae-framework, implementing the Signal Protocol for secure messaging.

## Features

- 🔒 **End-to-End Encryption**: Messages are encrypted using the Double Ratchet algorithm
- 🔑 **Perfect Forward Secrecy**: Past messages remain secure even if keys are compromised
- ✅ **Security Number Verification**: QR code and manual verification of contact identities
- 🔄 **Key Rotation**: Automatic key rotation for enhanced security
- 📱 **Multi-Device Support**: Secure synchronization across devices
- 🚀 **Real-time Messaging**: WebSocket-based real-time communication
- 🛡️ **Zero-Knowledge Architecture**: Server cannot decrypt messages

## Technology Stack

- **Frontend**: Next.js 14, React 18, TypeScript
- **Encryption**: libsodium (WebCrypto API)
- **Protocol**: Double Ratchet Algorithm (Signal Protocol)
- **Backend**: Node.js, PostgreSQL, Redis
- **Testing**: Vitest, Playwright
- **Deployment**: Docker, Kubernetes

## Quick Start

### Prerequisites

- Node.js 18+
- Docker and Docker Compose
- PostgreSQL 15+
- Redis 7+

### Installation

```bash
# Clone the repository
git clone https://github.com/yourusername/e2e-chat.git
cd e2e-chat

# Install dependencies
npm install

# Set up environment variables
cp .env.example .env.local

# Run database migrations
npm run db:migrate

# Start development server
npm run dev
```

### Docker Deployment

```bash
# Build and run with Docker Compose
docker-compose up -d

# Access the application
open http://localhost:3000
```

## Architecture

### Encryption Flow

1. **Key Generation**: Each user generates identity keys, signed pre-keys, and one-time pre-keys
2. **Session Establishment**: X3DH key agreement protocol establishes initial shared secret
3. **Message Encryption**: Double Ratchet provides forward secrecy and break-in recovery
4. **Secure Delivery**: Encrypted messages transmitted through secure WebSocket connections

### Security Properties

- **Confidentiality**: Only intended recipients can decrypt messages
- **Integrity**: Messages cannot be tampered with
- **Authentication**: Verify sender identity through security numbers
- **Forward Secrecy**: Compromise of long-term keys doesn't affect past sessions
- **Future Secrecy**: Compromise of session keys doesn't affect future messages

## Testing

```bash
# Run unit tests
npm test

# Run integration tests
npm run test:integration

# Run E2E tests
npm run test:e2e

# Generate coverage report
npm run test:coverage
```

## Security Considerations

- All cryptographic operations use libsodium
- Keys are stored encrypted in secure local storage
- Server has zero knowledge of message contents
- Regular security audits and penetration testing
- Compliance with GDPR and data protection regulations

## Contributing

Please read [CONTRIBUTING.md](CONTRIBUTING.md) for details on our code of conduct and the process for submitting pull requests.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- Signal Protocol for the encryption foundation
- ae-framework for the development methodology
- Open source cryptography community