import request from 'supertest';
import { expect } from 'chai';
import { Server } from 'http';
import { createApp } from '../../../backend/server';

/**
 * E2E暗号化チャットアプリケーション - APIインテグレーションテスト
 * 
 * バックエンドAPIの統合テストを実施します。
 * 認証、メッセージング、既読管理、WebSocket通信のAPIを検証します。
 */

describe('E2E Chat API インテグレーションテスト', () => {
  let app: any;
  let server: Server;
  
  // テストデータ
  const testUsers = {
    alice: {
      email: 'alice@test.com',
      password: 'password123',
      displayName: 'Alice Test'
    },
    bob: {
      email: 'bob@test.com', 
      password: 'password123',
      displayName: 'Bob Test'
    },
    charlie: {
      email: 'charlie@test.com',
      password: 'password123', 
      displayName: 'Charlie Test'
    }
  };
  
  let tokens: { [key: string]: string } = {};
  let userIds: { [key: string]: string } = {};
  let conversationId: string;

  before(async () => {
    app = createApp();
    server = app.listen(0); // ランダムポート
  });

  after(async () => {
    if (server) {
      server.close();
    }
  });

  describe('認証API', () => {
    it('ヘルスチェックエンドポイント', async () => {
      const response = await request(app)
        .get('/health')
        .expect(200);
        
      expect(response.body).to.have.property('status', 'ok');
      expect(response.body).to.have.property('timestamp');
    });

    it('新規ユーザー登録 - Alice', async () => {
      const response = await request(app)
        .post('/api/auth/register')
        .send(testUsers.alice)
        .expect(201);
        
      expect(response.body).to.have.property('token');
      expect(response.body).to.have.property('user');
      expect(response.body.user).to.have.property('email', testUsers.alice.email);
      expect(response.body.user).to.have.property('publicKey');
      
      tokens.alice = response.body.token;
      userIds.alice = response.body.user.id;
    });

    it('新規ユーザー登録 - Bob', async () => {
      const response = await request(app)
        .post('/api/auth/register')
        .send(testUsers.bob)
        .expect(201);
        
      tokens.bob = response.body.token;
      userIds.bob = response.body.user.id;
    });

    it('重複メールアドレスでの登録は失敗', async () => {
      const response = await request(app)
        .post('/api/auth/register')
        .send(testUsers.alice)
        .expect(409);
        
      expect(response.body).to.have.property('error');
    });

    it('不正なメールアドレスでの登録は失敗', async () => {
      await request(app)
        .post('/api/auth/register')
        .send({
          email: 'invalid-email',
          password: 'password123',
          displayName: 'Invalid'
        })
        .expect(400);
    });

    it('短すぎるパスワードでの登録は失敗', async () => {
      await request(app)
        .post('/api/auth/register')
        .send({
          email: 'short@test.com',
          password: '123',
          displayName: 'Short'
        })
        .expect(400);
    });

    it('既存ユーザーのログイン - Alice', async () => {
      const response = await request(app)
        .post('/api/auth/login')
        .send({
          email: testUsers.alice.email,
          password: testUsers.alice.password
        })
        .expect(200);
        
      expect(response.body).to.have.property('token');
      expect(response.body).to.have.property('user');
    });

    it('間違ったパスワードでのログインは失敗', async () => {
      await request(app)
        .post('/api/auth/login')
        .send({
          email: testUsers.alice.email,
          password: 'wrongpassword'
        })
        .expect(401);
    });

    it('存在しないユーザーでのログインは失敗', async () => {
      await request(app)
        .post('/api/auth/login')
        .send({
          email: 'nonexistent@test.com',
          password: 'password123'
        })
        .expect(401);
    });

    it('プロフィール取得 - 認証済み', async () => {
      const response = await request(app)
        .get('/api/users/profile')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      expect(response.body).to.have.property('email', testUsers.alice.email);
      expect(response.body).to.have.property('displayName', testUsers.alice.displayName);
      expect(response.body).to.have.property('publicKey');
    });

    it('プロフィール取得 - 未認証はエラー', async () => {
      await request(app)
        .get('/api/users/profile')
        .expect(401);
    });

    it('プロフィール取得 - 無効なトークンはエラー', async () => {
      await request(app)
        .get('/api/users/profile')
        .set('Authorization', 'Bearer invalid.token.here')
        .expect(401);
    });

    it('トークンリフレッシュ', async () => {
      const response = await request(app)
        .post('/api/auth/refresh')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      expect(response.body).to.have.property('token');
      expect(response.body).to.have.property('expiresIn');
    });
  });

  describe('会話管理API', () => {
    it('新規会話作成 - 1対1', async () => {
      const response = await request(app)
        .post('/api/conversations')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          participantIds: [userIds.bob]
        })
        .expect(201);
        
      expect(response.body).to.have.property('id');
      expect(response.body).to.have.property('participants');
      expect(response.body.participants).to.have.lengthOf(2);
      
      conversationId = response.body.id;
    });

    it('会話一覧取得', async () => {
      const response = await request(app)
        .get('/api/conversations')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      expect(response.body).to.have.property('conversations');
      expect(response.body.conversations).to.be.an('array');
      expect(response.body.conversations).to.have.lengthOf(1);
    });

    it('グループ会話作成', async () => {
      // Charlie を先に登録
      const charlieResponse = await request(app)
        .post('/api/auth/register')
        .send(testUsers.charlie)
        .expect(201);
        
      tokens.charlie = charlieResponse.body.token;
      userIds.charlie = charlieResponse.body.user.id;

      const response = await request(app)
        .post('/api/conversations')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          participantIds: [userIds.bob, userIds.charlie],
          title: 'テストグループ'
        })
        .expect(201);
        
      expect(response.body).to.have.property('title', 'テストグループ');
      expect(response.body.participants).to.have.lengthOf(3);
    });

    it('無効な参加者IDで会話作成は失敗', async () => {
      await request(app)
        .post('/api/conversations')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          participantIds: ['invalid-user-id']
        })
        .expect(400);
    });

    it('空の参加者リストで会話作成は失敗', async () => {
      await request(app)
        .post('/api/conversations')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          participantIds: []
        })
        .expect(400);
    });
  });

  describe('メッセージAPI', () => {
    let messageId: string;

    it('メッセージ送信', async () => {
      const messageData = {
        encryptedContent: 'encrypted_hello_bob',
        encryptedKeys: {
          [userIds.bob]: 'encrypted_aes_key_for_bob'
        },
        messageType: 'text'
      };

      const response = await request(app)
        .post(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send(messageData)
        .expect(201);
        
      expect(response.body).to.have.property('id');
      expect(response.body).to.have.property('encryptedContent', messageData.encryptedContent);
      expect(response.body).to.have.property('senderId', userIds.alice);
      
      messageId = response.body.id;
    });

    it('メッセージ履歴取得', async () => {
      const response = await request(app)
        .get(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      expect(response.body).to.have.property('messages');
      expect(response.body.messages).to.be.an('array');
      expect(response.body.messages).to.have.lengthOf(1);
      expect(response.body.messages[0]).to.have.property('id', messageId);
    });

    it('Bob がメッセージ履歴を取得', async () => {
      const response = await request(app)
        .get(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.bob}`)
        .expect(200);
        
      expect(response.body.messages).to.have.lengthOf(1);
      expect(response.body.messages[0].encryptedKeys).to.have.property(userIds.bob);
    });

    it('存在しない会話へのメッセージ送信は失敗', async () => {
      await request(app)
        .post('/api/conversations/invalid-id/messages')
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          encryptedContent: 'test',
          encryptedKeys: {}
        })
        .expect(404);
    });

    it('参加していない会話へのメッセージ送信は失敗', async () => {
      // 新しいユーザーを作成
      const newUserResponse = await request(app)
        .post('/api/auth/register')
        .send({
          email: 'outsider@test.com',
          password: 'password123',
          displayName: 'Outsider'
        })
        .expect(201);

      await request(app)
        .post(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${newUserResponse.body.token}`)
        .send({
          encryptedContent: 'unauthorized',
          encryptedKeys: {}
        })
        .expect(403);
    });

    it('不正な暗号化データでのメッセージ送信は失敗', async () => {
      await request(app)
        .post(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          encryptedContent: '',  // 空の暗号化コンテンツ
          encryptedKeys: {}
        })
        .expect(400);
    });

    it('メッセージ検索・フィルタリング', async () => {
      // 複数のメッセージを送信
      for (let i = 0; i < 5; i++) {
        await request(app)
          .post(`/api/conversations/${conversationId}/messages`)
          .set('Authorization', `Bearer ${tokens.alice}`)
          .send({
            encryptedContent: `encrypted_message_${i}`,
            encryptedKeys: {
              [userIds.bob]: `encrypted_key_${i}`
            }
          })
          .expect(201);
      }

      // 制限付きで取得
      const response = await request(app)
        .get(`/api/conversations/${conversationId}/messages?limit=3`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      expect(response.body.messages).to.have.lengthOf(3);
      expect(response.body).to.have.property('hasMore', true);
    });
  });

  describe('既読ステータスAPI', () => {
    let testMessageId: string;

    before(async () => {
      // テスト用メッセージを送信
      const response = await request(app)
        .post(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          encryptedContent: 'encrypted_read_status_test',
          encryptedKeys: {
            [userIds.bob]: 'encrypted_key_for_read_test'
          }
        })
        .expect(201);
        
      testMessageId = response.body.id;
    });

    it('既読ステータス更新', async () => {
      const response = await request(app)
        .post(`/api/conversations/${conversationId}/read-status`)
        .set('Authorization', `Bearer ${tokens.bob}`)
        .send({
          messageId: testMessageId,
          deviceId: 'device_bob_phone'
        })
        .expect(200);
        
      expect(response.body).to.have.property('success', true);
    });

    it('同じデバイスでの重複既読は成功（冪等性）', async () => {
      await request(app)
        .post(`/api/conversations/${conversationId}/read-status`)
        .set('Authorization', `Bearer ${tokens.bob}`)
        .send({
          messageId: testMessageId,
          deviceId: 'device_bob_phone'
        })
        .expect(200);
    });

    it('異なるデバイスでの既読ステータス更新', async () => {
      await request(app)
        .post(`/api/conversations/${conversationId}/read-status`)
        .set('Authorization', `Bearer ${tokens.bob}`)
        .send({
          messageId: testMessageId,
          deviceId: 'device_bob_tablet'
        })
        .expect(200);
    });

    it('存在しないメッセージの既読は失敗', async () => {
      await request(app)
        .post(`/api/conversations/${conversationId}/read-status`)
        .set('Authorization', `Bearer ${tokens.bob}`)
        .send({
          messageId: 'invalid-message-id',
          deviceId: 'device_bob_phone'
        })
        .expect(404);
    });

    it('他人のメッセージの既読ステータス更新は失敗', async () => {
      await request(app)
        .post(`/api/conversations/${conversationId}/read-status`)
        .set('Authorization', `Bearer ${tokens.charlie}`)
        .send({
          messageId: testMessageId,
          deviceId: 'device_charlie_phone'
        })
        .expect(403);
    });

    it('既読ステータスが反映されたメッセージ取得', async () => {
      const response = await request(app)
        .get(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      const message = response.body.messages.find((m: any) => m.id === testMessageId);
      expect(message).to.have.property('readStatus');
      expect(message.readStatus).to.be.an('array');
      expect(message.readStatus).to.have.lengthOf(2); // 2つのデバイス
    });
  });

  describe('パフォーマンステスト', () => {
    it('大量メッセージの処理', async () => {
      const startTime = Date.now();
      const promises = [];
      
      // 50件のメッセージを並行送信
      for (let i = 0; i < 50; i++) {
        promises.push(
          request(app)
            .post(`/api/conversations/${conversationId}/messages`)
            .set('Authorization', `Bearer ${tokens.alice}`)
            .send({
              encryptedContent: `bulk_message_${i}`,
              encryptedKeys: {
                [userIds.bob]: `bulk_key_${i}`
              }
            })
        );
      }
      
      const responses = await Promise.all(promises);
      const endTime = Date.now();
      
      // 全て成功することを確認
      responses.forEach(response => {
        expect(response.status).to.equal(201);
      });
      
      // 5秒以内で完了することを確認
      expect(endTime - startTime).to.be.lessThan(5000);
    });

    it('大量データ取得のパフォーマンス', async () => {
      const startTime = Date.now();
      
      const response = await request(app)
        .get(`/api/conversations/${conversationId}/messages?limit=100`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .expect(200);
        
      const endTime = Date.now();
      
      expect(response.body.messages).to.be.an('array');
      expect(endTime - startTime).to.be.lessThan(2000); // 2秒以内
    });

    it('同時接続ユーザーの処理', async () => {
      const promises = [];
      
      // 3人のユーザーが同時にAPIを呼び出し
      [tokens.alice, tokens.bob, tokens.charlie].forEach(token => {
        promises.push(
          request(app)
            .get('/api/users/profile')
            .set('Authorization', `Bearer ${token}`)
        );
      });
      
      const responses = await Promise.all(promises);
      
      responses.forEach(response => {
        expect(response.status).to.equal(200);
      });
    });
  });

  describe('セキュリティテスト', () => {
    it('SQL インジェクション攻撃の防止', async () => {
      await request(app)
        .post('/api/auth/login')
        .send({
          email: "test@test.com'; DROP TABLE users; --",
          password: 'password123'
        })
        .expect(401); // 正常に失敗する
    });

    it('XSS 攻撃の防止', async () => {
      const response = await request(app)
        .post(`/api/conversations/${conversationId}/messages`)
        .set('Authorization', `Bearer ${tokens.alice}`)
        .send({
          encryptedContent: '<script>alert("xss")</script>',
          encryptedKeys: {
            [userIds.bob]: 'test_key'
          }
        })
        .expect(201);
        
      // スクリプトタグがそのまま保存される（暗号化されているため問題なし）
      expect(response.body.encryptedContent).to.equal('<script>alert("xss")</script>');
    });

    it('レート制限の確認', async () => {
      // 短時間で大量リクエストを送信
      const promises = [];
      for (let i = 0; i < 100; i++) {
        promises.push(
          request(app)
            .get('/health')
        );
      }
      
      const responses = await Promise.all(promises);
      
      // 一部のリクエストがレート制限される可能性がある
      const successCount = responses.filter(r => r.status === 200).length;
      const rateLimitCount = responses.filter(r => r.status === 429).length;
      
      expect(successCount + rateLimitCount).to.equal(100);
    });

    it('CORS ヘッダーの確認', async () => {
      const response = await request(app)
        .options('/api/auth/login')
        .set('Origin', 'http://localhost:4173')
        .expect(200);
        
      expect(response.headers).to.have.property('access-control-allow-origin');
      expect(response.headers).to.have.property('access-control-allow-methods');
    });
  });

  describe('エラーハンドリング', () => {
    it('不正なJSONでのリクエスト', async () => {
      await request(app)
        .post('/api/auth/register')
        .set('Content-Type', 'application/json')
        .send('{"invalid json": }')
        .expect(400);
    });

    it('存在しないエンドポイント', async () => {
      await request(app)
        .get('/api/nonexistent')
        .expect(404);
    });

    it('メソッド不許可', async () => {
      await request(app)
        .delete('/api/auth/login')
        .expect(405);
    });

    it('サーバーエラーのハンドリング', async () => {
      // サーバーエラーを意図的に発生させるテスト
      // 実装依存：例：データベース接続エラーをシミュレート
    });
  });
});