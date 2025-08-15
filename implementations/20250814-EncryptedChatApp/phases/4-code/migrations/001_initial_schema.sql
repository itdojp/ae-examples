-- E2E暗号化チャットアプリケーション 初期データベーススキーマ
-- 作成日: 2025年8月14日
-- バージョン: 1.0

-- ユーザーテーブル
CREATE TABLE IF NOT EXISTS users (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    display_name VARCHAR(100) NOT NULL,
    public_key TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
    last_login_at TIMESTAMP NULL,
    is_active BOOLEAN DEFAULT TRUE,
    
    INDEX idx_users_email (email),
    INDEX idx_users_active (is_active),
    INDEX idx_users_created_at (created_at)
);

-- 会話テーブル
CREATE TABLE IF NOT EXISTS conversations (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    title VARCHAR(255) NULL,
    type ENUM('direct', 'group') DEFAULT 'direct',
    created_by VARCHAR(36) NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE,
    
    FOREIGN KEY (created_by) REFERENCES users(id) ON DELETE CASCADE,
    INDEX idx_conversations_type (type),
    INDEX idx_conversations_created_by (created_by),
    INDEX idx_conversations_active (is_active)
);

-- 会話参加者テーブル
CREATE TABLE IF NOT EXISTS conversation_participants (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    conversation_id VARCHAR(36) NOT NULL,
    user_id VARCHAR(36) NOT NULL,
    joined_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    left_at TIMESTAMP NULL,
    role ENUM('member', 'admin') DEFAULT 'member',
    is_active BOOLEAN DEFAULT TRUE,
    
    FOREIGN KEY (conversation_id) REFERENCES conversations(id) ON DELETE CASCADE,
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE,
    UNIQUE KEY unique_active_participant (conversation_id, user_id, is_active),
    INDEX idx_participants_conversation (conversation_id),
    INDEX idx_participants_user (user_id),
    INDEX idx_participants_active (is_active)
);

-- メッセージテーブル
CREATE TABLE IF NOT EXISTS messages (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    conversation_id VARCHAR(36) NOT NULL,
    sender_id VARCHAR(36) NOT NULL,
    encrypted_content TEXT NOT NULL,
    message_type ENUM('text', 'image', 'file') DEFAULT 'text',
    sent_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    edited_at TIMESTAMP NULL,
    is_deleted BOOLEAN DEFAULT FALSE,
    
    FOREIGN KEY (conversation_id) REFERENCES conversations(id) ON DELETE CASCADE,
    FOREIGN KEY (sender_id) REFERENCES users(id) ON DELETE CASCADE,
    INDEX idx_messages_conversation (conversation_id),
    INDEX idx_messages_sender (sender_id),
    INDEX idx_messages_sent_at (sent_at),
    INDEX idx_messages_type (message_type),
    INDEX idx_messages_deleted (is_deleted)
);

-- 暗号化キーテーブル（受信者別）
CREATE TABLE IF NOT EXISTS message_keys (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    message_id VARCHAR(36) NOT NULL,
    recipient_id VARCHAR(36) NOT NULL,
    encrypted_key TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE CASCADE,
    FOREIGN KEY (recipient_id) REFERENCES users(id) ON DELETE CASCADE,
    UNIQUE KEY unique_message_recipient (message_id, recipient_id),
    INDEX idx_message_keys_message (message_id),
    INDEX idx_message_keys_recipient (recipient_id)
);

-- デバイステーブル
CREATE TABLE IF NOT EXISTS devices (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    user_id VARCHAR(36) NOT NULL,
    device_id VARCHAR(255) NOT NULL,
    device_name VARCHAR(100) NULL,
    device_type ENUM('mobile', 'desktop', 'tablet', 'web') DEFAULT 'web',
    user_agent TEXT NULL,
    ip_address VARCHAR(45) NULL,
    first_seen_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    last_seen_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE,
    
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE,
    UNIQUE KEY unique_user_device (user_id, device_id),
    INDEX idx_devices_user (user_id),
    INDEX idx_devices_active (is_active),
    INDEX idx_devices_last_seen (last_seen_at)
);

-- 既読ステータステーブル
CREATE TABLE IF NOT EXISTS read_status (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    message_id VARCHAR(36) NOT NULL,
    user_id VARCHAR(36) NOT NULL,
    device_id VARCHAR(36) NOT NULL,
    read_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE CASCADE,
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE,
    FOREIGN KEY (device_id) REFERENCES devices(id) ON DELETE CASCADE,
    UNIQUE KEY unique_message_user_device (message_id, user_id, device_id),
    INDEX idx_read_status_message (message_id),
    INDEX idx_read_status_user (user_id),
    INDEX idx_read_status_device (device_id),
    INDEX idx_read_status_read_at (read_at)
);

-- セッションテーブル（オプション：JWTの代わりにDB管理する場合）
CREATE TABLE IF NOT EXISTS user_sessions (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    user_id VARCHAR(36) NOT NULL,
    device_id VARCHAR(36) NOT NULL,
    session_token VARCHAR(255) UNIQUE NOT NULL,
    expires_at TIMESTAMP NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    last_activity_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE,
    
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE,
    FOREIGN KEY (device_id) REFERENCES devices(id) ON DELETE CASCADE,
    INDEX idx_sessions_user (user_id),
    INDEX idx_sessions_device (device_id),
    INDEX idx_sessions_token (session_token),
    INDEX idx_sessions_expires (expires_at),
    INDEX idx_sessions_active (is_active)
);

-- ファイルアップロードテーブル（将来の機能拡張用）
CREATE TABLE IF NOT EXISTS file_uploads (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    message_id VARCHAR(36) NOT NULL,
    original_filename VARCHAR(255) NOT NULL,
    stored_filename VARCHAR(255) NOT NULL,
    mime_type VARCHAR(100) NOT NULL,
    file_size BIGINT NOT NULL,
    encrypted_file_key TEXT NOT NULL,
    uploaded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    FOREIGN KEY (message_id) REFERENCES messages(id) ON DELETE CASCADE,
    INDEX idx_file_uploads_message (message_id),
    INDEX idx_file_uploads_uploaded_at (uploaded_at)
);

-- 監査ログテーブル
CREATE TABLE IF NOT EXISTS audit_logs (
    id VARCHAR(36) PRIMARY KEY DEFAULT (uuid()),
    user_id VARCHAR(36) NULL,
    action VARCHAR(100) NOT NULL,
    resource_type VARCHAR(50) NOT NULL,
    resource_id VARCHAR(36) NULL,
    details JSON NULL,
    ip_address VARCHAR(45) NULL,
    user_agent TEXT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE SET NULL,
    INDEX idx_audit_logs_user (user_id),
    INDEX idx_audit_logs_action (action),
    INDEX idx_audit_logs_resource (resource_type, resource_id),
    INDEX idx_audit_logs_created_at (created_at)
);

-- 初期データ挿入
INSERT INTO users (id, email, password_hash, display_name, public_key) VALUES
('550e8400-e29b-41d4-a716-446655440001', 'test@example.com', '$2a$10$placeholder_hash_for_password123', 'Test User', '-----BEGIN PUBLIC KEY-----\nplaceholder_public_key\n-----END PUBLIC KEY-----');

-- トリガー：updated_at の自動更新
DELIMITER $$

CREATE TRIGGER update_users_timestamp 
    BEFORE UPDATE ON users 
    FOR EACH ROW 
BEGIN
    SET NEW.updated_at = CURRENT_TIMESTAMP;
END$$

CREATE TRIGGER update_conversations_timestamp 
    BEFORE UPDATE ON conversations 
    FOR EACH ROW 
BEGIN
    SET NEW.updated_at = CURRENT_TIMESTAMP;
END$$

DELIMITER ;

-- ビュー：会話の最新メッセージ
CREATE VIEW conversation_latest_messages AS
SELECT 
    c.id as conversation_id,
    c.title,
    c.type,
    m.id as latest_message_id,
    m.encrypted_content as latest_message_content,
    m.message_type as latest_message_type,
    m.sent_at as latest_message_time,
    u.display_name as latest_sender_name,
    (
        SELECT COUNT(*) 
        FROM messages m2 
        WHERE m2.conversation_id = c.id 
        AND m2.is_deleted = FALSE
    ) as total_messages
FROM conversations c
LEFT JOIN messages m ON m.id = (
    SELECT m2.id 
    FROM messages m2 
    WHERE m2.conversation_id = c.id 
    AND m2.is_deleted = FALSE 
    ORDER BY m2.sent_at DESC 
    LIMIT 1
)
LEFT JOIN users u ON m.sender_id = u.id
WHERE c.is_active = TRUE;

-- ビュー：未読メッセージ数
CREATE VIEW unread_message_counts AS
SELECT 
    cp.user_id,
    cp.conversation_id,
    COUNT(m.id) as unread_count
FROM conversation_participants cp
JOIN messages m ON m.conversation_id = cp.conversation_id
LEFT JOIN read_status rs ON rs.message_id = m.id AND rs.user_id = cp.user_id
WHERE cp.is_active = TRUE
AND m.is_deleted = FALSE
AND m.sender_id != cp.user_id  -- 自分のメッセージは除外
AND rs.id IS NULL  -- 既読レコードが存在しないもの
GROUP BY cp.user_id, cp.conversation_id;

-- インデックス最適化のための統計情報更新
ANALYZE TABLE users, conversations, conversation_participants, messages, message_keys, devices, read_status;

-- データベースバージョン記録
CREATE TABLE IF NOT EXISTS schema_versions (
    version VARCHAR(20) PRIMARY KEY,
    applied_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    description TEXT
);

INSERT INTO schema_versions (version, description) VALUES 
('001', 'Initial schema for E2E encrypted chat application');

COMMIT;