package e2echat

import future.keywords.contains
import future.keywords.if
import future.keywords.in

# Default deny
default allow := false

# Allow health check endpoint for everyone
allow if {
    input.path == "/health"
    input.method == "GET"
}

# Allow Swagger documentation access
allow if {
    input.path == "/docs"
    input.method == "GET"
}

# Allow authentication endpoints for unauthenticated users
allow if {
    input.path == "/auth/register"
    input.method == "POST"
    not input.user
}

allow if {
    input.path == "/auth/login"
    input.method == "POST"
    not input.user
}

# Allow authenticated users to access their own data
allow if {
    input.user.id
    input.method == "GET"
    input.path == sprintf("/users/%s", [input.user.id])
}

# Allow authenticated users to enable 2FA
allow if {
    input.user.id
    input.path == "/auth/2fa/enable"
    input.method == "POST"
}

# Allow authenticated users to verify 2FA
allow if {
    input.user.id
    input.path == "/auth/2fa/verify"
    input.method == "POST"
}

# Key Management Policies

# Allow authenticated users to upload their own keys
allow if {
    input.user.id
    input.path == "/keys/upload"
    input.method == "POST"
}

# Allow authenticated users to get any user's public key bundle
allow if {
    input.user.id
    input.path[_] == "keys"
    input.path[_] == "bundle"
    input.method == "GET"
}

# Allow authenticated users to rotate their own signed pre-key
allow if {
    input.user.id
    input.path == "/keys/rotate/signed"
    input.method == "POST"
}

# Allow authenticated users to request one-time pre-keys
allow if {
    input.user.id
    input.path[_] == "keys"
    input.path[_] == "one-time"
    input.method == "POST"
}

# Messaging Policies

# Allow authenticated users to send messages
allow if {
    input.user.id
    input.path == "/messages/send"
    input.method == "POST"
}

# Allow authenticated users to retrieve messages
allow if {
    input.user.id
    input.path[_] == "messages"
    input.method == "GET"
}

# Allow authenticated users to send receipts
allow if {
    input.user.id
    input.path[_] == "messages"
    input.path[_] == "receipt"
    input.method == "POST"
}

# Session Management Policies

# Allow authenticated users to establish sessions
allow if {
    input.user.id
    input.path[_] == "sessions"
    input.method == "POST"
}

# Allow authenticated users to get session info
allow if {
    input.user.id
    input.path[_] == "sessions"
    input.method == "GET"
}

# Verification Policies

# Allow authenticated users to get safety numbers
allow if {
    input.user.id
    input.path[_] == "verification"
    input.path[_] == "safety-number"
    input.method == "GET"
}

# Allow authenticated users to verify other users
allow if {
    input.user.id
    input.path[_] == "verification"
    input.path[_] == "verify"
    input.method == "POST"
}

# WebSocket connection - only authenticated users
allow if {
    input.user.id
    input.path == "/ws"
    input.method == "UPGRADE"
}

# Rate Limiting Rules

# Define rate limits per endpoint
rate_limits := {
    "/auth/register": {"requests": 5, "window": "1h"},
    "/auth/login": {"requests": 10, "window": "15m"},
    "/messages/send": {"requests": 100, "window": "1m"},
    "/keys/upload": {"requests": 10, "window": "1h"},
}

rate_limit_exceeded if {
    limit := rate_limits[input.path]
    input.request_count > limit.requests
}

# Privacy Rules

# Users can only access their own message history
message_access_allowed if {
    input.user.id
    input.resource.type == "message"
    input.user.id in [input.resource.senderId, input.resource.recipientId]
}

# Users can only modify their own keys
key_modification_allowed if {
    input.user.id
    input.resource.type == "key"
    input.resource.userId == input.user.id
}

# Device Management Rules

# Users can only manage their own devices
device_access_allowed if {
    input.user.id
    input.resource.type == "device"
    input.resource.userId == input.user.id
}

# Audit Requirements

# Actions that require audit logging
audit_required if {
    input.action in [
        "user.register",
        "user.login",
        "user.2fa.enable",
        "message.send",
        "message.decrypt",
        "key.rotate",
        "session.establish",
        "user.verify"
    ]
}

# Security Policies

# Enforce secure password requirements
password_policy_met if {
    input.password
    count(input.password) >= 12
    regex.match("[A-Z]", input.password)
    regex.match("[a-z]", input.password)
    regex.match("[0-9]", input.password)
    regex.match("[!@#$%^&*(),.?\":{}|<>]", input.password)
}

# Enforce device fingerprint for login
device_fingerprint_required if {
    input.path == "/auth/login"
    input.method == "POST"
    not input.body.deviceFingerprint
}

# Data Retention Policies

# Messages older than retention period should be deleted
message_retention_days := 90

message_should_be_deleted if {
    input.resource.type == "message"
    time.now_ns() - input.resource.timestamp > (message_retention_days * 24 * 60 * 60 * 1000000000)
}

# One-time keys that have been used should be deleted
one_time_key_should_be_deleted if {
    input.resource.type == "one_time_key"
    input.resource.used == true
}

# Compliance Rules

# GDPR - Users can request their own data
gdpr_data_access_allowed if {
    input.user.id
    input.action == "data.export"
    input.resource.userId == input.user.id
}

# GDPR - Users can request deletion of their account
gdpr_deletion_allowed if {
    input.user.id
    input.action == "account.delete"
    input.resource.userId == input.user.id
}

# Helper Functions

# Check if user has verified another user
user_verified(userId, peerId) if {
    verification := data.verifications[userId][peerId]
    verification.verified == true
}

# Check if a session exists between two users
session_exists(userId1, userId2) if {
    session := data.sessions[userId1][userId2]
    session.established == true
}

# Check if user has 2FA enabled
two_fa_enabled(userId) if {
    user := data.users[userId]
    user.twoFactorEnabled == true
}

# Validate JWT token expiration
token_valid if {
    input.token.exp > time.now_ns() / 1000000000
}