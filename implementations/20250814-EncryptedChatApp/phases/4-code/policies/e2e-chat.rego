# E2E暗号化チャットアプリケーション - Open Policy Agent (OPA) ポリシー
# 認可・アクセス制御ルール定義

package e2echat

import rego.v1

# デフォルト拒否ポリシー
default allow := false

# ユーザー認証確認
authenticated_user := user if {
    token := input.token
    user := jwt.decode_verify(token, {"secret": data.jwt_secret})[1]
}

# 管理者権限確認
is_admin := true if {
    authenticated_user.role == "admin"
}

# ユーザー登録許可
allow if {
    input.action == "register"
    input.method == "POST"
    input.path == "/api/auth/register"
}

# ログイン許可
allow if {
    input.action == "login"
    input.method == "POST" 
    input.path == "/api/auth/login"
}

# ヘルスチェック許可
allow if {
    input.action == "health_check"
    input.method == "GET"
    input.path == "/health"
}

# 認証済みユーザーのプロフィールアクセス
allow if {
    input.action == "get_profile"
    input.method == "GET"
    input.path == "/api/users/profile"
    authenticated_user
}

# プロフィール更新（本人のみ）
allow if {
    input.action == "update_profile"
    input.method == "PUT"
    input.path == "/api/users/profile"
    authenticated_user
    authenticated_user.id == input.user_id
}

# 会話作成許可
allow if {
    input.action == "create_conversation"
    input.method == "POST"
    input.path == "/api/conversations"
    authenticated_user
    valid_participants
}

# 会話一覧取得（自分が参加している会話のみ）
allow if {
    input.action == "list_conversations"
    input.method == "GET"
    input.path == "/api/conversations"
    authenticated_user
}

# 会話詳細取得（参加者のみ）
allow if {
    input.action == "get_conversation"
    input.method == "GET"
    startswith(input.path, "/api/conversations/")
    authenticated_user
    is_conversation_participant
}

# メッセージ送信（会話参加者のみ）
allow if {
    input.action == "send_message"
    input.method == "POST"
    regex.match(`^/api/conversations/[^/]+/messages$`, input.path)
    authenticated_user
    is_conversation_participant
    valid_message_content
}

# メッセージ履歴取得（会話参加者のみ）
allow if {
    input.action == "get_messages"
    input.method == "GET"
    regex.match(`^/api/conversations/[^/]+/messages`, input.path)
    authenticated_user
    is_conversation_participant
}

# 既読ステータス更新（メッセージ受信者のみ）
allow if {
    input.action == "update_read_status"
    input.method == "POST"
    regex.match(`^/api/conversations/[^/]+/read-status$`, input.path)
    authenticated_user
    is_message_recipient
}

# 管理者専用：全ユーザー一覧
allow if {
    input.action == "list_all_users"
    input.method == "GET"
    input.path == "/api/admin/users"
    is_admin
}

# 管理者専用：システム統計
allow if {
    input.action == "get_system_stats"
    input.method == "GET"
    input.path == "/api/admin/stats"
    is_admin
}

# === ヘルパー関数 ===

# 会話参加者確認
is_conversation_participant := true if {
    conversation_id := extract_conversation_id(input.path)
    conversation_id in data.user_conversations[authenticated_user.id]
}

# メッセージ受信者確認
is_message_recipient := true if {
    conversation_id := extract_conversation_id(input.path)
    message_id := input.body.messageId
    authenticated_user.id in data.message_recipients[message_id]
}

# 有効な参加者リスト確認
valid_participants := true if {
    input.body.participantIds
    count(input.body.participantIds) > 0
    count(input.body.participantIds) <= 100  # 最大100人
    all_participants_exist
}

# 全参加者が存在することを確認
all_participants_exist := true if {
    all_exist := [participant_id |
        participant_id := input.body.participantIds[_]
        participant_id in data.existing_users
    ]
    count(all_exist) == count(input.body.participantIds)
}

# 有効なメッセージ内容確認
valid_message_content := true if {
    input.body.encryptedContent
    input.body.encryptedKeys
    count(input.body.encryptedContent) > 0
    count(input.body.encryptedKeys) > 0
    input.body.messageType in ["text", "image", "file"]
}

# パスから会話IDを抽出
extract_conversation_id(path) := conversation_id if {
    parts := split(path, "/")
    parts[2] == "conversations"
    conversation_id := parts[3]
}

# === セキュリティポリシー ===

# レート制限チェック
rate_limit_exceeded := true if {
    user_id := authenticated_user.id
    current_requests := data.rate_limits[user_id].current_hour_requests
    current_requests > data.rate_limits[user_id].max_requests_per_hour
}

# 拒否：レート制限超過
deny[msg] if {
    rate_limit_exceeded
    msg := "Rate limit exceeded. Too many requests per hour."
}

# IP制限チェック
ip_blocked := true if {
    input.client_ip in data.blocked_ips
}

# 拒否：ブロックされたIP
deny[msg] if {
    ip_blocked
    msg := "Access denied from blocked IP address."
}

# 暗号化要件チェック
encryption_required := true if {
    input.action in ["send_message", "create_conversation"]
    not input.body.encryptedContent
}

# 拒否：暗号化なしメッセージ
deny[msg] if {
    encryption_required
    msg := "All messages must be encrypted."
}

# メッセージサイズ制限
message_too_large := true if {
    input.action == "send_message"
    count(input.body.encryptedContent) > data.limits.max_message_size
}

# 拒否：メッセージサイズ超過
deny[msg] if {
    message_too_large
    msg := sprintf("Message size exceeds limit of %d bytes.", [data.limits.max_message_size])
}

# ファイルタイプ制限
invalid_file_type := true if {
    input.action == "send_message"
    input.body.messageType == "file"
    not input.body.mimeType in data.allowed_file_types
}

# 拒否：許可されていないファイルタイプ
deny[msg] if {
    invalid_file_type
    msg := sprintf("File type not allowed: %s", [input.body.mimeType])
}

# === 監査ログ ===

# アクセス許可の監査ログ
audit_log := {
    "timestamp": time.now_ns(),
    "user_id": authenticated_user.id,
    "action": input.action,
    "resource": input.path,
    "method": input.method,
    "client_ip": input.client_ip,
    "user_agent": input.user_agent,
    "allowed": allow,
    "deny_reasons": deny
} if {
    authenticated_user
}

# セキュリティイベントログ
security_event := {
    "timestamp": time.now_ns(),
    "event_type": "security_violation",
    "details": {
        "action": input.action,
        "path": input.path,
        "client_ip": input.client_ip,
        "user_agent": input.user_agent,
        "violation_reasons": deny
    }
} if {
    count(deny) > 0
}

# === データ構造例 ===
# data.jwt_secret: "your-secret-key"
# data.user_conversations: {
#   "user-id-1": ["conv-1", "conv-2"],
#   "user-id-2": ["conv-1", "conv-3"]
# }
# data.message_recipients: {
#   "message-id-1": ["user-id-1", "user-id-2"]
# }
# data.existing_users: ["user-id-1", "user-id-2", "user-id-3"]
# data.blocked_ips: ["192.168.1.100", "10.0.0.5"]
# data.limits: {
#   "max_message_size": 10485760,  // 10MB
#   "max_participants": 100
# }
# data.allowed_file_types: [
#   "image/jpeg", "image/png", "image/gif",
#   "application/pdf", "text/plain"
# ]
# data.rate_limits: {
#   "user-id-1": {
#     "max_requests_per_hour": 1000,
#     "current_hour_requests": 50
#   }
# }