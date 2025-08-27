# E2E Encrypted Chat Application

🔐 A secure messaging application with end-to-end encryption using the Signal Protocol architecture.

## 📋 Features

- **End-to-End Encryption**: Messages are encrypted on the sender's device and only decrypted on the recipient's device
- **Perfect Forward Secrecy**: Each message uses unique encryption keys
- **User Authentication**: Secure registration and login system
- **Real-time Messaging**: WebSocket-based instant messaging
- **Encryption Status Indicators**: Visual feedback for encryption status
- **Responsive Design**: Modern UI built with React and Tailwind CSS

## 🚀 Quick Start

### Prerequisites

- Node.js 18+ 
- pnpm (recommended) or npm
- Docker (optional, for containerized deployment)

### Installation & Running

#### Method 1: Local Development

1. **Clone and navigate to the project**:
```bash
cd e2e-chat-app
```

2. **Install dependencies**:
```bash
pnpm install
# or
npm install
```

3. **Build shared types**:
```bash
cd shared && pnpm build && cd ..
# or
cd shared && npm run build && cd ..
```

4. **Start the backend server**:
```bash
cd backend
pnpm dev
# or
npm run dev
```
Backend will run on http://localhost:3001

5. **In a new terminal, start the frontend**:
```bash
cd frontend
pnpm dev
# or
npm run dev
```
Frontend will run on http://localhost:3000

#### Method 2: Using Docker

1. **Build and run with Docker Compose**:
```bash
docker-compose up --build
```

2. **Access the application**:
- Frontend: http://localhost:3000
- Backend API: http://localhost:3001

## 🎯 How to Use

### 1. Register an Account

1. Open http://localhost:3000
2. Click "Register"
3. Enter your details:
   - Display Name (e.g., "Alice")
   - Email address
   - Password (minimum 8 characters)
4. Click "Create Account"

Your encryption keys will be automatically generated upon registration.

### 2. Login

1. Go to the login page
2. Enter your email and password
3. Click "Sign In"

### 3. Send Encrypted Messages

1. After logging in, you'll see the chat interface
2. Select a user from the contacts list on the left
3. Type your message in the input field
4. Click "Send" or press Enter
5. Messages are automatically encrypted before sending

### 4. Verify Encryption

- Look for the 🔒 icon in the chat header
- Green indicator = Active encryption
- Yellow indicator = Establishing encryption
- Red indicator = Encryption error

## 🔐 Security Features

### Encryption Implementation

- **Algorithm**: TweetNaCl (NaCl crypto library)
- **Key Exchange**: X25519 Elliptic Curve Diffie-Hellman
- **Message Encryption**: XSalsa20-Poly1305
- **Key Generation**: Automatic on registration
- **Pre-Keys**: 100 one-time pre-keys generated for asynchronous messaging

### Security Best Practices

1. **Never share your private keys**
2. **Use strong, unique passwords**
3. **Verify security fingerprints for important conversations**
4. **Keep your browser and dependencies updated**

## 🏗️ Architecture

```
e2e-chat-app/
├── backend/          # Node.js Express server
│   ├── routes/       # API endpoints
│   ├── services/     # Crypto & database services
│   └── socket/       # WebSocket handlers
├── frontend/         # React application
│   ├── components/   # UI components
│   ├── services/     # API & crypto services
│   └── stores/       # State management (Zustand)
└── shared/           # Shared TypeScript types
```

## 🧪 Testing the Encryption

To verify encryption is working:

1. **Open browser developer tools** (F12)
2. **Go to Network tab**
3. **Send a message**
4. **Check the WebSocket messages** - you should see encrypted ciphertext, not plain text

Example of encrypted message payload:
```json
{
  "ciphertext": "base64-encrypted-content",
  "nonce": "base64-nonce",
  "authTag": "authentication-tag"
}
```

## ⚠️ Important Notes

### Development vs Production

This is a **demonstration application** showing E2E encryption concepts. For production use:

1. **Use a real database** (PostgreSQL/MongoDB) instead of in-memory storage
2. **Implement proper key management** and secure storage
3. **Add rate limiting** and DDoS protection
4. **Implement proper session management**
5. **Add comprehensive logging and monitoring**
6. **Conduct security audits** and penetration testing
7. **Use environment variables** for all secrets
8. **Implement backup key recovery mechanisms**

### Known Limitations

- In-memory database (data is lost on server restart)
- Simplified key exchange (no Double Ratchet algorithm yet)
- No group chat support
- No file/media encryption
- No message history sync across devices

## 📚 Technical Details

### Backend Technologies
- Node.js + TypeScript
- Express.js
- Socket.io
- TweetNaCl for cryptography
- JWT for authentication

### Frontend Technologies
- React 18
- TypeScript
- Vite
- Tailwind CSS
- Socket.io-client
- Zustand for state management

### Cryptographic Libraries
- tweetnacl: Implementation of NaCl crypto
- tweetnacl-util: Utilities for encoding/decoding

## 🤝 Contributing

This is a demonstration project for the ae-framework implementation. Feel free to:

1. Report bugs
2. Suggest improvements
3. Submit pull requests
4. Use as a learning resource

## 📄 License

MIT License - See LICENSE file for details

## 🔗 Related Documentation

- [ae-framework Documentation](../docs/)
- [Signal Protocol Specification](https://signal.org/docs/)
- [TweetNaCl Documentation](https://tweetnacl.js.org/)

---

**Security Notice**: This application demonstrates E2E encryption concepts. Always conduct proper security audits before deploying cryptographic systems in production.