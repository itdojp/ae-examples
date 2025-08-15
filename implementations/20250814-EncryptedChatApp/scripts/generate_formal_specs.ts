import { FormalAgent } from './ae-framework/src/agents/formal-agent.js';
import { readFileSync } from 'fs';
import path from 'path';

async function generateE2EChatFormalSpecs() {
  try {
    console.log('🔧 Formal Agent を使用してE2E暗号化チャットアプリケーションの形式仕様を生成します...\n');

    // Intent Agent の分析結果を読み込み（要件仕様書から主要要件を抽出）
    const requirementsPath = path.join(__dirname, 'E2E_EncryptedChatApplicationRequirementsSpecification.md');
    const requirementsContent = readFileSync(requirementsPath, 'utf-8');

    // Formal Agent のインスタンスを作成
    const agent = new FormalAgent({
      outputFormat: 'tla+',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true
    });

    console.log('📋 分析された主要セキュリティ要件:');
    const securityRequirements = `
E2E Encrypted Chat System Formal Specification

CONSTANTS: MaxUsers, MaxMessages, MaxKeys
VARIABLES: users, messages, keys, sessions

Message security requirements:
- All messages must be encrypted with AES-256-GCM
- Message keys are ephemeral and deleted after use
- Perfect Forward Secrecy through Double Ratchet protocol

Key management requirements:
- Each user has identity keys, signed prekeys, one-time prekeys
- Key exchange uses X25519 ECDH
- Digital signatures use Ed25519
- Session keys rotate regularly

Authentication requirements:
- Multi-factor authentication required
- Device registration and fingerprinting
- Trusted device management

System invariants:
- Messages are never stored in plaintext
- Private keys never leave secure storage
- Authentication precedes all operations
    `;

    // 1. TLA+ 形式仕様の生成
    console.log('\n🎯 1. TLA+ 形式仕様の生成...');
    const tlaSpec = await agent.generateFormalSpecification(
      securityRequirements,
      'tla+',
      { 
        includeDiagrams: true, 
        generateProperties: true,
        includeInvariants: true 
      }
    );

    // 2. OpenAPI 仕様の生成
    console.log('🎯 2. OpenAPI 仕様の生成...');
    const apiRequirements = `
E2E暗号化チャットAPI要件:

エンドポイント:
- POST /auth/login - ユーザー認証 (メール、パスワード、2FA)
- POST /auth/register - ユーザー登録
- POST /keys/generate - 鍵ペア生成
- POST /keys/exchange - 鍵交換プロトコル  
- POST /messages - 暗号化メッセージ送信
- GET /messages/:channelId - メッセージ取得
- POST /channels - チャンネル作成
- GET /devices - デバイス一覧取得
- POST /devices/trust - デバイス信頼設定

セキュリティ:
- すべてのエンドポイントでJWT認証
- メッセージペイロードは事前暗号化済み
- 鍵交換はX25519+Ed25519プロトコル
- レート制限とDDoS保護
    `;

    const apiSpec = await agent.createAPISpecification(
      apiRequirements,
      'openapi',
      { 
        includeExamples: true, 
        generateContracts: true,
        includeSecurity: true 
      }
    );

    // 3. 状態機械の生成
    console.log('🎯 3. メッセージ処理状態機械の生成...');
    const stateMachineReqs = `
メッセージ処理ワークフロー:

状態:
- Created: メッセージ作成
- Encrypted: 暗号化完了
- Transmitted: 送信完了  
- Delivered: 配信完了
- Read: 既読確認
- Deleted: 削除済み

遷移:
- Created -> Encrypted: encrypt(message, recipientKey)
- Encrypted -> Transmitted: send(encryptedMessage)
- Transmitted -> Delivered: acknowledge(messageId)
- Delivered -> Read: markAsRead(messageId)
- Any -> Deleted: delete(messageId)

不変条件:
- メッセージは暗号化後のみ送信可能
- 削除されたメッセージは復元不可
- 既読確認は配信後のみ可能
    `;

    const stateMachine = await agent.generateStateMachine(
      stateMachineReqs,
      { 
        generateInvariants: true, 
        includeDiagrams: true,
        generateProperties: true 
      }
    );

    // 4. 契約仕様の生成
    console.log('🎯 4. 暗号化契約仕様の生成...');
    const encryptionContract = await agent.createContracts(
      'function encryptMessage(plaintext: string, recipientPublicKey: PublicKey): EncryptedMessage',
      `
暗号化関数の要件:
- 事前条件: plaintext は非空文字列、recipientPublicKey は有効な公開鍵
- 事後条件: 返り値は AES-256-GCM で暗号化されたメッセージ
- 不変条件: 暗号化により平文は復元不可能
- 例外処理: 無効な鍵の場合は CryptographicError を発生
      `,
      { 
        includeInvariants: true,
        includeExceptionHandling: true 
      }
    );

    // 5. AsyncAPI 仕様の生成 (リアルタイム通信用)
    console.log('🎯 5. AsyncAPI 仕様の生成...');
    const asyncApiReqs = `
リアルタイムメッセージング要件:

チャンネル:
- messages/{userId} - 個人宛メッセージ受信
- typing/{channelId} - タイピング状態通知  
- presence/{userId} - オンライン状態更新
- keys/exchange - 鍵交換イベント

メッセージ:
- MessageReceived: 暗号化メッセージ受信イベント
- TypingStatus: タイピング状態変更
- PresenceUpdate: オンライン/オフライン状態
- KeyExchangeRequest: 鍵交換リクエスト
- KeyExchangeResponse: 鍵交換レスポンス

プロトコル: WebSocket over TLS 1.3
    `;

    const asyncApiSpec = await agent.createAPISpecification(
      asyncApiReqs,
      'asyncapi',
      { 
        includeExamples: true,
        generateContracts: true 
      }
    );

    // 6. 仕様の検証
    console.log('🎯 6. 生成された仕様の検証...');
    
    // TLA+ 仕様の検証
    const tlaValidation = await agent.validateSpecification(tlaSpec);

    // モデルチェック実行
    const modelCheckResult = await agent.runModelChecking(
      tlaSpec,
      [
        'SafetyProperty', 
        'TypeInvariant', 
        'MessageIntegrity',
        'KeySecrecy'
      ],
      { timeout: 30000 }
    );

    // 7. 図表の生成
    console.log('🎯 7. UML図表の生成...');
    const diagrams = await agent.generateDiagrams(
      tlaSpec,
      ['sequence', 'state', 'class', 'component']
    );

    // 結果の出力
    console.log('\n' + '='.repeat(80));
    console.log('📋 FORMAL SPECIFICATION GENERATION REPORT');
    console.log('='.repeat(80));

    console.log('\n✅ 生成された形式仕様:');
    console.log(`1. TLA+ 仕様: ${tlaSpec.content.split('\n').length} 行`);
    console.log(`2. OpenAPI 仕様: ${JSON.stringify(apiSpec).length} 文字`);
    console.log(`3. AsyncAPI 仕様: ${JSON.stringify(asyncApiSpec).length} 文字`);
    console.log(`4. 状態機械: ${stateMachine.states.length} 状態, ${stateMachine.transitions.length} 遷移`);
    console.log(`5. 契約仕様: ${encryptionContract.length} 契約`);
    console.log(`6. UML図表: ${diagrams.length} 図表`);

    console.log('\n📊 検証結果:');
    console.log(`TLA+ 仕様検証: ${tlaValidation.status}`);
    if (tlaValidation.errors.length > 0) {
      console.log(`検証エラー: ${tlaValidation.errors.length} 件`);
    }
    if (tlaValidation.warnings.length > 0) {
      console.log(`検証警告: ${tlaValidation.warnings.length} 件`);
    }

    console.log('\n🔍 モデルチェック結果:');
    modelCheckResult.properties.forEach((prop, index) => {
      const status = prop.satisfied ? '✅' : '❌';
      console.log(`${index + 1}. ${prop.name}: ${status} ${prop.description}`);
      if (!prop.satisfied && prop.counterExample) {
        console.log(`   反例: ${prop.counterExample.description}`);
      }
    });

    console.log(`\n📈 統計情報:`);
    console.log(`探索状態数: ${modelCheckResult.statistics.statesExplored}`);
    console.log(`実行時間: ${modelCheckResult.statistics.timeElapsed}ms`);
    console.log(`メモリ使用量: ${(modelCheckResult.statistics.memoryUsed / 1024).toFixed(2)}KB`);

    console.log('\n' + '='.repeat(80));
    console.log('✅ 形式仕様生成が完了しました。');
    console.log('='.repeat(80));

    // 結果を返す
    return {
      tlaSpec,
      apiSpec,
      asyncApiSpec,
      stateMachine,
      encryptionContract,
      diagrams,
      validation: tlaValidation,
      modelCheck: modelCheckResult
    };

  } catch (error) {
    console.error('❌ 形式仕様生成中にエラーが発生しました:', error);
    throw error;
  }
}

// 実行
generateE2EChatFormalSpecs().catch(console.error);