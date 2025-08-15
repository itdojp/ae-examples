-- E2E Encrypted Chat Database Schema
-- PostgreSQL migration file for initial schema

-- Users table
CREATE TABLE IF NOT EXISTS users (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    display_name VARCHAR(100) NOT NULL,
    is_verified BOOLEAN DEFAULT FALSE,
    last_seen TIMESTAMPTZ,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_created_at ON users(created_at);

-- Devices table
CREATE TABLE IF NOT EXISTS devices (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    device_fingerprint VARCHAR(255) NOT NULL,
    name VARCHAR(100),
    trust_level VARCHAR(20) NOT NULL CHECK (trust_level IN ('trusted', 'untrusted', 'revoked')),
    last_activity TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(user_id, device_fingerprint)
);

CREATE INDEX idx_devices_user_id ON devices(user_id);
CREATE INDEX idx_devices_trust_level ON devices(trust_level);

-- Identity keys table
CREATE TABLE IF NOT EXISTS identity_keys (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID UNIQUE NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    public_key TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_identity_keys_user_id ON identity_keys(user_id);

-- Signed pre-keys table
CREATE TABLE IF NOT EXISTS signed_pre_keys (
    id SERIAL PRIMARY KEY,
    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    key_id INTEGER NOT NULL,
    public_key TEXT NOT NULL,
    signature TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    expires_at TIMESTAMPTZ NOT NULL,
    UNIQUE(user_id, key_id)
);

CREATE INDEX idx_signed_pre_keys_user_id ON signed_pre_keys(user_id);
CREATE INDEX idx_signed_pre_keys_expires_at ON signed_pre_keys(expires_at);

-- One-time pre-keys table
CREATE TABLE IF NOT EXISTS one_time_pre_keys (
    id SERIAL PRIMARY KEY,
    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    key_id INTEGER NOT NULL,
    public_key TEXT NOT NULL,
    used BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(user_id, key_id)
);

CREATE INDEX idx_one_time_pre_keys_user_id ON one_time_pre_keys(user_id);
CREATE INDEX idx_one_time_pre_keys_used ON one_time_pre_keys(used);

-- Sessions table
CREATE TABLE IF NOT EXISTS sessions (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    peer_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    root_key TEXT NOT NULL,
    sending_chain_key TEXT,
    receiving_chain_key TEXT,
    sending_message_number INTEGER DEFAULT 0,
    receiving_message_number INTEGER DEFAULT 0,
    previous_sending_chain_length INTEGER DEFAULT 0,
    dh_sending_public_key TEXT,
    dh_sending_private_key TEXT,
    dh_receiving_key TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(user_id, peer_id)
);

CREATE INDEX idx_sessions_user_id ON sessions(user_id);
CREATE INDEX idx_sessions_peer_id ON sessions(peer_id);
CREATE INDEX idx_sessions_updated_at ON sessions(updated_at);

-- Messages table
CREATE TABLE IF NOT EXISTS messages (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    sender_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    recipient_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    session_id UUID NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
    ciphertext TEXT NOT NULL,
    nonce TEXT NOT NULL,
    auth_tag TEXT NOT NULL,
    dh_public_key TEXT,
    message_number INTEGER NOT NULL,
    previous_chain_length INTEGER NOT NULL,
    delivered BOOLEAN DEFAULT FALSE,
    read BOOLEAN DEFAULT FALSE,
    timestamp TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_messages_sender_id ON messages(sender_id);
CREATE INDEX idx_messages_recipient_id ON messages(recipient_id);
CREATE INDEX idx_messages_session_id ON messages(session_id);
CREATE INDEX idx_messages_timestamp ON messages(timestamp);
CREATE INDEX idx_messages_delivered ON messages(delivered);
CREATE INDEX idx_messages_read ON messages(read);

-- Message receipts table
CREATE TABLE IF NOT EXISTS message_receipts (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    message_id UUID NOT NULL REFERENCES messages(id) ON DELETE CASCADE,
    recipient_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    status VARCHAR(20) NOT NULL CHECK (status IN ('sent', 'delivered', 'read')),
    timestamp TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(message_id, recipient_id, status)
);

CREATE INDEX idx_message_receipts_message_id ON message_receipts(message_id);
CREATE INDEX idx_message_receipts_recipient_id ON message_receipts(recipient_id);

-- Safety numbers table
CREATE TABLE IF NOT EXISTS safety_numbers (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id_1 UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    user_id_2 UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    number TEXT NOT NULL,
    qr_code TEXT NOT NULL,
    verified BOOLEAN DEFAULT FALSE,
    verified_at TIMESTAMPTZ,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    CONSTRAINT check_user_order CHECK (user_id_1 < user_id_2),
    UNIQUE(user_id_1, user_id_2)
);

CREATE INDEX idx_safety_numbers_user_id_1 ON safety_numbers(user_id_1);
CREATE INDEX idx_safety_numbers_user_id_2 ON safety_numbers(user_id_2);
CREATE INDEX idx_safety_numbers_verified ON safety_numbers(verified);

-- Auth tokens table
CREATE TABLE IF NOT EXISTS auth_tokens (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    device_id UUID NOT NULL REFERENCES devices(id) ON DELETE CASCADE,
    token_hash VARCHAR(255) NOT NULL,
    refresh_token_hash VARCHAR(255) NOT NULL,
    expires_at TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(token_hash)
);

CREATE INDEX idx_auth_tokens_user_id ON auth_tokens(user_id);
CREATE INDEX idx_auth_tokens_device_id ON auth_tokens(device_id);
CREATE INDEX idx_auth_tokens_expires_at ON auth_tokens(expires_at);

-- Two-factor authentication table
CREATE TABLE IF NOT EXISTS two_factor_auth (
    user_id UUID PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    secret TEXT NOT NULL,
    backup_codes TEXT[] NOT NULL,
    enabled BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Skipped message keys table (for Double Ratchet)
CREATE TABLE IF NOT EXISTS skipped_message_keys (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    session_id UUID NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
    dh_public_key TEXT NOT NULL,
    message_number INTEGER NOT NULL,
    message_key TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    UNIQUE(session_id, dh_public_key, message_number)
);

CREATE INDEX idx_skipped_message_keys_session_id ON skipped_message_keys(session_id);

-- Function to update updated_at timestamp
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ language 'plpgsql';

-- Create triggers for updated_at
CREATE TRIGGER update_users_updated_at BEFORE UPDATE ON users
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_sessions_updated_at BEFORE UPDATE ON sessions
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_two_factor_auth_updated_at BEFORE UPDATE ON two_factor_auth
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();