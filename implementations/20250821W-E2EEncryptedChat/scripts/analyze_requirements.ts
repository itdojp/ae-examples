import { IntentAgent, IntentAnalysisRequest } from './ae-framework/src/agents/intent-agent.js';
import { readFileSync } from 'fs';
import path from 'path';

async function analyzeE2EChatRequirements() {
  try {
    // 要件仕様書を読み込み
    const requirementsPath = path.join(__dirname, 'E2E_EncryptedChatApplicationRequirementsSpecification.md');
    const requirementsContent = readFileSync(requirementsPath, 'utf-8');

    // Intent Agentのインスタンスを作成
    const agent = new IntentAgent();

    // 分析リクエストを構成
    const request: IntentAnalysisRequest = {
      sources: [
        {
          type: 'document',
          content: requirementsContent,
          metadata: {
            author: 'System',
            title: 'E2E Encrypted Chat Application Requirements Specification',
            version: '1.0',
            date: new Date('2025-08-08'),
            tags: ['security', 'encryption', 'chat', 'e2e']
          }
        }
      ],
      context: {
        domain: 'Secure Messaging & Communication',
        existingSystem: false,
        constraints: [
          {
            type: 'security',
            description: 'Must implement end-to-end encryption with Perfect Forward Secrecy',
            impact: 'high'
          },
          {
            type: 'compliance',
            description: 'GDPR compliance required for EU users',
            impact: 'high'
          },
          {
            type: 'technical',
            description: 'Cross-platform support (iOS 14+, Android 10+, Web)',
            impact: 'medium'
          }
        ],
        stakeholders: [
          {
            name: 'Security Team',
            role: 'Security Architect',
            concerns: ['Cryptographic strength', 'Key management', 'Attack resistance'],
            influenceLevel: 'high'
          },
          {
            name: 'Product Team',
            role: 'Product Manager',
            concerns: ['User experience', 'Feature completeness', 'Market readiness'],
            influenceLevel: 'high'
          },
          {
            name: 'Development Team',
            role: 'Technical Lead',
            concerns: ['Implementation complexity', 'Performance', 'Maintainability'],
            influenceLevel: 'high'
          },
          {
            name: 'Compliance Team',
            role: 'Legal Advisor',
            concerns: ['Regulatory compliance', 'Data protection', 'Privacy'],
            influenceLevel: 'medium'
          }
        ],
        glossary: [
          {
            term: 'E2E Encryption',
            definition: 'End-to-end encryption where only sender and receiver can decrypt messages',
            context: 'Prevents third parties including service providers from reading message content'
          },
          {
            term: 'Perfect Forward Secrecy',
            definition: 'Property ensuring past communications remain secure even if long-term keys are compromised',
            context: 'Achieved through ephemeral key exchange and regular key rotation'
          },
          {
            term: 'Double Ratchet',
            definition: 'Cryptographic protocol providing forward secrecy and self-healing properties',
            context: 'Used in Signal Protocol for secure messaging'
          }
        ]
      },
      analysisDepth: 'comprehensive'
    };

    console.log('🔍 E2E暗号化チャットアプリケーション要件分析を開始します...\n');

    // Intent分析を実行
    const result = await agent.analyzeIntent(request);

    console.log('✅ 分析が完了しました。結果を表示します:\n');

    // 分析結果を構造化して表示
    console.log('='.repeat(80));
    console.log('📋 INTENT ANALYSIS REPORT - E2E暗号化チャットアプリケーション');
    console.log('='.repeat(80));
    console.log();

    // 要件サマリー
    console.log('📄 REQUIREMENTS SUMMARY');
    console.log('-'.repeat(40));
    console.log(`総要件数: ${result.requirements.length}`);
    console.log(`機能要件: ${result.requirements.filter(r => r.type === 'functional').length}`);
    console.log(`非機能要件: ${result.requirements.filter(r => r.type === 'non-functional').length}`);
    console.log(`セキュリティ要件: ${result.requirements.filter(r => r.category.includes('security') || r.category.includes('暗号')).length}`);
    console.log();

    // 優先度別要件分布
    console.log('🎯 REQUIREMENTS BY PRIORITY');
    console.log('-'.repeat(40));
    const priorityCounts = result.requirements.reduce((acc, req) => {
      acc[req.priority] = (acc[req.priority] || 0) + 1;
      return acc;
    }, {} as Record<string, number>);
    
    Object.entries(priorityCounts).forEach(([priority, count]) => {
      console.log(`${priority.toUpperCase()}: ${count}件`);
    });
    console.log();

    // 主要要件リスト
    console.log('📝 KEY REQUIREMENTS');
    console.log('-'.repeat(40));
    result.requirements.slice(0, 10).forEach((req, index) => {
      console.log(`${index + 1}. [${req.id}] ${req.description}`);
      console.log(`   優先度: ${req.priority} | カテゴリ: ${req.category} | タイプ: ${req.type}`);
      console.log();
    });

    // ユーザーストーリー
    console.log('👥 USER STORIES');
    console.log('-'.repeat(40));
    result.userStories.forEach((story, index) => {
      console.log(`${index + 1}. ${story.title}`);
      console.log(`   ${story.narrative.asA}として、${story.narrative.iWant}したい。${story.narrative.soThat}のため。`);
      console.log(`   優先度: ${story.priority} | ポイント: ${story.points || 'TBD'}`);
      console.log();
    });

    // ドメインモデル
    console.log('🏗️ DOMAIN MODEL');
    console.log('-'.repeat(40));
    console.log(`エンティティ数: ${result.domainModel.entities.length}`);
    console.log(`関係数: ${result.domainModel.relationships.length}`);
    console.log(`境界コンテキスト数: ${result.domainModel.boundedContexts.length}`);
    console.log();
    
    console.log('主要エンティティ:');
    result.domainModel.entities.slice(0, 8).forEach((entity, index) => {
      console.log(`${index + 1}. ${entity.name}`);
      console.log(`   属性: ${entity.attributes.map(a => a.name).join(', ')}`);
      console.log();
    });

    // 制約事項
    console.log('⚠️ CONSTRAINTS');
    console.log('-'.repeat(40));
    result.constraints.forEach((constraint, index) => {
      console.log(`${index + 1}. [${constraint.type.toUpperCase()}] ${constraint.description}`);
      console.log(`   影響度: ${constraint.impact} | カテゴリ: ${constraint.category || 'N/A'}`);
      console.log();
    });

    // リスク分析
    console.log('🚨 RISK ANALYSIS');
    console.log('-'.repeat(40));
    result.risks.forEach((risk, index) => {
      console.log(`${index + 1}. ${risk.description}`);
      console.log(`   カテゴリ: ${risk.category} | 影響度: ${risk.impact} | 確率: ${risk.probability}`);
      if (risk.mitigation) {
        console.log(`   対策: ${risk.mitigation}`);
      }
      console.log();
    });

    // 曖昧性検出
    if (result.ambiguities.length > 0) {
      console.log('🔍 AMBIGUITIES DETECTED');
      console.log('-'.repeat(40));
      result.ambiguities.forEach((ambiguity, index) => {
        console.log(`${index + 1}. [${ambiguity.severity.toUpperCase()}] ${ambiguity.type}`);
        console.log(`   テキスト: "${ambiguity.text}"`);
        console.log(`   場所: ${ambiguity.location}`);
        console.log(`   推奨対策: ${ambiguity.suggestion}`);
        console.log();
      });
    }

    // 仮定事項
    console.log('🤔 ASSUMPTIONS');
    console.log('-'.repeat(40));
    result.assumptions.forEach((assumption, index) => {
      console.log(`${index + 1}. ${assumption.description}`);
      console.log(`   タイプ: ${assumption.type} | 信頼度: ${assumption.confidence}`);
      if (assumption.validationMethod) {
        console.log(`   検証方法: ${assumption.validationMethod}`);
      }
      console.log();
    });

    // 改善提案
    if (result.suggestions.length > 0) {
      console.log('💡 SUGGESTIONS FOR IMPROVEMENT');
      console.log('-'.repeat(40));
      result.suggestions.forEach((suggestion, index) => {
        console.log(`${index + 1}. ${suggestion}`);
      });
      console.log();
    }

    console.log('='.repeat(80));
    console.log('✅ Intent分析が完了しました。');
    console.log('='.repeat(80));

    return result;

  } catch (error) {
    console.error('❌ 要件分析中にエラーが発生しました:', error);
    throw error;
  }
}

// 実行
analyzeE2EChatRequirements().catch(console.error);