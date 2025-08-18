# E2E Encrypted Chat - API Documentation

## Overview

The E2E Encrypted Chat API provides secure messaging capabilities with end-to-end encryption. All message content is encrypted on the client side before transmission.

**Base URL**: `https://api.e2echat.com`  
**WebSocket URL**: `wss://ws.e2echat.com`

## Authentication

All API requests require authentication using JWT tokens.

```http
Authorization: Bearer <token>
```

### Obtain Token

```graphql
mutation Login($email: String!, $password: String!, $totp: String) {
  login(email: $email, password: $password, totp: $totp) {
    token
    refreshToken
    user {
      id
      email
      displayName
    }
  }
}
```

## GraphQL Schema

### User Operations

#### Register User
```graphql
mutation RegisterUser($input: RegisterInput!) {
  register(input: $input) {
    user {
      id
      email
      displayName
      createdAt
    }
    keyBundle {
      identityKey
      signedPreKey
      preKeySignature
    }
  }
}

input RegisterInput {
  email: String!
  password: String!
  displayName: String!
  publicKeys: KeyBundleInput!
}

input KeyBundleInput {
  identityKey: String!
  signedPreKey: String!
  preKeySignature: String!
  oneTimePreKeys: [String!]!
}
```

#### Get User Profile
```graphql
query GetUser($id: ID!) {
  user(id: $id) {
    id
    displayName
    avatar
    status
    lastSeen
    publicKey
    devices {
      id
      name
      lastActive
    }
  }
}
```

### Message Operations

#### Send Message
```graphql
mutation SendMessage($input: SendMessageInput!) {
  sendMessage(input: $input) {
    id
    timestamp
    status
  }
}

input SendMessageInput {
  recipientId: ID!
  encryptedContent: String!
  nonce: String!
  ephemeralKey: String
  messageNumber: Int!
}
```

#### Get Messages
```graphql
query GetMessages($chatId: ID!, $limit: Int, $before: String) {
  messages(chatId: $chatId, limit: $limit, before: $before) {
    edges {
      node {
        id
        senderId
        encryptedContent
        nonce
        timestamp
        status
        ephemeralKey
      }
      cursor
    }
    pageInfo {
      hasNextPage
      endCursor
    }
  }
}
```

### Key Management

#### Upload Pre-Keys
```graphql
mutation UploadPreKeys($keys: [String!]!) {
  uploadPreKeys(keys: $keys) {
    success
    count
  }
}
```

#### Fetch Pre-Key Bundle
```graphql
query FetchPreKeyBundle($userId: ID!) {
  preKeyBundle(userId: $userId) {
    identityKey
    signedPreKey
    preKeySignature
    oneTimePreKey
  }
}
```

### Session Management

#### Establish Session
```graphql
mutation EstablishSession($recipientId: ID!, $initialMessage: String!) {
  establishSession(
    recipientId: $recipientId, 
    initialMessage: $initialMessage
  ) {
    sessionId
    fingerprint
  }
}
```

#### Verify Session
```graphql
mutation VerifySession($sessionId: ID!, $securityNumber: String!) {
  verifySession(
    sessionId: $sessionId, 
    securityNumber: $securityNumber
  ) {
    verified
    verifiedAt
  }
}
```

## WebSocket Events

### Connection
```javascript
const socket = io('wss://ws.e2echat.com', {
  auth: {
    token: 'jwt-token'
  }
});
```

### Events

#### Message Events
```javascript
// Receive new message
socket.on('message:new', (data) => {
  /*
  {
    id: string,
    senderId: string,
    encryptedContent: string,
    nonce: string,
    timestamp: number,
    ephemeralKey?: string
  }
  */
});

// Message delivered
socket.on('message:delivered', (data) => {
  /*
  {
    messageId: string,
    deliveredAt: number
  }
  */
});

// Message read
socket.on('message:read', (data) => {
  /*
  {
    messageId: string,
    readAt: number
  }
  */
});
```

#### Typing Indicators
```javascript
// Send typing indicator
socket.emit('typing:start', { chatId: 'chat-id' });
socket.emit('typing:stop', { chatId: 'chat-id' });

// Receive typing indicator
socket.on('typing:update', (data) => {
  /*
  {
    userId: string,
    chatId: string,
    isTyping: boolean
  }
  */
});
```

#### Presence
```javascript
// User online
socket.on('presence:online', (data) => {
  /*
  {
    userId: string,
    timestamp: number
  }
  */
});

// User offline
socket.on('presence:offline', (data) => {
  /*
  {
    userId: string,
    lastSeen: number
  }
  */
});
```

## REST Endpoints

### Health Check
```http
GET /health
```

Response:
```json
{
  "status": "healthy",
  "version": "1.0.0",
  "timestamp": 1234567890
}
```

### Upload Avatar
```http
POST /api/avatar
Content-Type: multipart/form-data

file: <binary>
```

Response:
```json
{
  "url": "https://cdn.e2echat.com/avatars/user-id.jpg"
}
```

### Export Messages
```http
GET /api/export/messages?format=json&chatId=chat-id
```

Response:
```json
{
  "messages": [
    {
      "id": "msg-1",
      "content": "<encrypted>",
      "timestamp": 1234567890
    }
  ],
  "exported_at": 1234567890
}
```

## Error Handling

### Error Response Format
```json
{
  "error": {
    "code": "ERROR_CODE",
    "message": "Human readable message",
    "details": {}
  }
}
```

### Common Error Codes

| Code | Description | HTTP Status |
|------|-------------|-------------|
| `AUTH_REQUIRED` | Authentication required | 401 |
| `AUTH_INVALID` | Invalid credentials | 401 |
| `AUTH_EXPIRED` | Token expired | 401 |
| `PERMISSION_DENIED` | Insufficient permissions | 403 |
| `NOT_FOUND` | Resource not found | 404 |
| `VALIDATION_ERROR` | Input validation failed | 400 |
| `RATE_LIMIT` | Rate limit exceeded | 429 |
| `SERVER_ERROR` | Internal server error | 500 |

## Rate Limiting

- **Authentication**: 5 requests per minute
- **Message sending**: 100 messages per minute
- **API calls**: 1000 requests per hour
- **WebSocket events**: 500 events per minute

Headers:
```http
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1234567890
```

## Encryption Details

### Message Encryption Format
```json
{
  "version": 1,
  "ciphertext": "base64-encoded-ciphertext",
  "nonce": "base64-encoded-nonce",
  "ephemeralKey": "base64-encoded-key",
  "mac": "base64-encoded-mac"
}
```

### Key Format
All keys are transmitted as base64-encoded strings:
- **Identity Keys**: Ed25519 public keys (32 bytes)
- **Pre-Keys**: X25519 public keys (32 bytes)
- **Signatures**: Ed25519 signatures (64 bytes)

## SDKs

### JavaScript/TypeScript
```bash
npm install @e2echat/sdk
```

```typescript
import { E2EChatClient } from '@e2echat/sdk';

const client = new E2EChatClient({
  apiUrl: 'https://api.e2echat.com',
  wsUrl: 'wss://ws.e2echat.com'
});

await client.login(email, password);
await client.sendMessage(recipientId, message);
```

### Python
```bash
pip install e2echat-sdk
```

```python
from e2echat import Client

client = Client(
    api_url="https://api.e2echat.com",
    ws_url="wss://ws.e2echat.com"
)

client.login(email, password)
client.send_message(recipient_id, message)
```

## Webhooks

Configure webhooks for server-side events:

```http
POST /api/webhooks
Content-Type: application/json

{
  "url": "https://your-server.com/webhook",
  "events": ["message.sent", "message.delivered"],
  "secret": "webhook-secret"
}
```

Webhook payload:
```json
{
  "event": "message.sent",
  "timestamp": 1234567890,
  "data": {},
  "signature": "hmac-sha256-signature"
}
```

## API Versioning

The API uses URL versioning. Current version: `v1`

Future versions will be available at:
- `https://api.e2echat.com/v2`
- `https://api.e2echat.com/v3`

## Support

- API Status: https://status.e2echat.com
- Documentation: https://docs.e2echat.com
- Support: api-support@e2echat.com