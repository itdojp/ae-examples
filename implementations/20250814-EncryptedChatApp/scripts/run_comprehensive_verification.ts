/**
 * Comprehensive Verification Script for E2E Chat Implementation
 * Using ae-framework Verify Agent for quality assurance
 */

import { VerifyAgent, type VerificationRequest, type CodeFile, type TestFile, type Specification } from './ae-framework/src/agents/verify-agent';
import { readFileSync, writeFileSync, existsSync, readdirSync, statSync } from 'fs';
import * as path from 'path';

async function runComprehensiveVerification() {
  console.log('🔍 ae-framework Verify Agent を使用して包括的品質検証を実行します...\n');

  const agent = new VerifyAgent({ 
    enableContainers: true,
    containerConfig: {
      preferredEngine: 'docker',
      buildImages: false
    }
  });

  // 1. プロジェクトファイルの収集
  console.log('📁 1. プロジェクトファイルの収集...');
  const projectPath = '/home/claudecode/work/ae-framework_test/e2e_chat_implementation';
  
  const codeFiles: CodeFile[] = await loadCodeFiles(projectPath);
  const testFiles: TestFile[] = await loadTestFiles(projectPath);
  const specifications: Specification[] = await loadSpecifications();

  console.log(`   📄 ソースファイル: ${codeFiles.length}件`);
  console.log(`   🧪 テストファイル: ${testFiles.length}件`);
  console.log(`   📋 仕様書: ${specifications.length}件\n`);

  // 2. 包括的検証設定
  const verificationRequest: VerificationRequest = {
    codeFiles,
    testFiles,
    specifications,
    verificationTypes: [
      'tests',
      'coverage',
      'linting',
      'typechecking',
      'security',
      'performance',
      'specifications',
      'contracts'
    ],
    strictMode: false, // すべての検証を実行
    containerConfig: {
      enabled: true,
      preferredEngine: 'docker',
      buildImages: false,
      projectPath
    }
  };

  try {
    // 3. 包括的検証の実行
    console.log('🔍 2. 包括的品質検証の実行...');
    const startTime = Date.now();
    
    const result = await agent.runFullVerification(verificationRequest);
    
    const duration = Date.now() - startTime;
    console.log(`   ⏱️ 検証時間: ${duration}ms\n`);

    // 4. 結果の分析と表示
    console.log('📊 3. 検証結果の分析...');
    displayVerificationResults(result);

    // 5. 詳細レポートの生成
    console.log('\n📝 4. 詳細レポートの生成...');
    await generateDetailedReport(result, projectPath);

    // 6. 推奨改善事項の表示
    console.log('\n💡 5. 推奨改善事項:');
    result.suggestions.forEach((suggestion, index) => {
      console.log(`   ${index + 1}. ${suggestion}`);
    });

    // 7. 品質ゲートの評価
    console.log('\n🚪 6. 品質ゲート評価:');
    evaluateQualityGates(result);

    console.log('\n================================================================================');
    console.log(`🛡️ COMPREHENSIVE VERIFICATION ${result.passed ? 'COMPLETED SUCCESSFULLY' : 'COMPLETED WITH ISSUES'}`);
    console.log('================================================================================');

  } catch (error) {
    console.error('❌ 検証中にエラーが発生しました:', error);
    process.exit(1);
  }
}

async function loadCodeFiles(projectPath: string): Promise<CodeFile[]> {
  const codeFiles: CodeFile[] = [];
  
  // Recursively find TypeScript/JavaScript files
  function findFiles(dir: string, extensions: string[]): string[] {
    const files: string[] = [];
    
    if (!existsSync(dir)) return files;
    
    const entries = readdirSync(dir);
    
    for (const entry of entries) {
      const fullPath = path.join(dir, entry);
      const stat = statSync(fullPath);
      
      if (stat.isDirectory() && !entry.startsWith('.') && entry !== 'node_modules') {
        files.push(...findFiles(fullPath, extensions));
      } else if (stat.isFile() && extensions.some(ext => entry.endsWith(ext))) {
        files.push(fullPath);
      }
    }
    
    return files;
  }

  const sourceFiles = findFiles(path.join(projectPath, 'src'), ['.ts', '.js', '.tsx', '.jsx']);
  
  for (const file of sourceFiles) {
    if (existsSync(file)) {
      const content = readFileSync(file, 'utf-8');
      const language = getLanguageFromExtension(path.extname(file));
      
      codeFiles.push({
        path: file,
        content,
        language
      });
    }
  }

  return codeFiles;
}

async function loadTestFiles(projectPath: string): Promise<TestFile[]> {
  const testFiles: TestFile[] = [];
  
  // Recursively find test files
  function findTestFiles(dir: string): string[] {
    const files: string[] = [];
    
    if (!existsSync(dir)) return files;
    
    const entries = readdirSync(dir);
    
    for (const entry of entries) {
      const fullPath = path.join(dir, entry);
      const stat = statSync(fullPath);
      
      if (stat.isDirectory() && !entry.startsWith('.') && entry !== 'node_modules') {
        files.push(...findTestFiles(fullPath));
      } else if (stat.isFile() && (entry.includes('.test.') || entry.includes('.spec.'))) {
        files.push(fullPath);
      }
    }
    
    return files;
  }

  // Search in common test directories
  const testDirs = ['tests', 'test', '__tests__'];
  
  for (const testDir of testDirs) {
    const testPath = path.join(projectPath, testDir);
    const files = findTestFiles(testPath);
    
    for (const file of files) {
      if (existsSync(file)) {
        const content = readFileSync(file, 'utf-8');
        const testType = determineTestType(file);
        
        testFiles.push({
          path: file,
          content,
          type: testType
        });
      }
    }
  }

  return testFiles;
}

async function loadSpecifications(): Promise<Specification[]> {
  const specifications: Specification[] = [];
  const specPath = '/home/claudecode/work/ae-framework_test/formal_specifications';
  
  // 形式仕様ファイルの読み込み
  const specFiles = [
    { file: 'E2E_Chat_API.json', type: 'openapi' as const },
    { file: 'E2E_Chat_AsyncAPI.json', type: 'asyncapi' as const },
    { file: 'E2E_Chat_Schema.graphql', type: 'graphql' as const },
    { file: 'E2E_Chat_Specification.tla', type: 'tla' as const }
  ];

  for (const { file, type } of specFiles) {
    const fullPath = path.join(specPath, file);
    if (existsSync(fullPath)) {
      const content = readFileSync(fullPath, 'utf-8');
      specifications.push({
        type,
        content,
        path: fullPath
      });
    }
  }

  return specifications;
}

function getLanguageFromExtension(ext: string): string {
  const languageMap: Record<string, string> = {
    '.ts': 'typescript',
    '.tsx': 'typescript',
    '.js': 'javascript',
    '.jsx': 'javascript'
  };
  return languageMap[ext] || 'unknown';
}

function determineTestType(filePath: string): 'unit' | 'integration' | 'e2e' | 'property' | 'contract' {
  const filename = path.basename(filePath).toLowerCase();
  
  if (filename.includes('pbt') || filename.includes('property')) {
    return 'property';
  }
  if (filename.includes('contract') || filename.includes('pact')) {
    return 'contract';
  }
  if (filename.includes('e2e') || filename.includes('end-to-end')) {
    return 'e2e';
  }
  if (filename.includes('integration') || filename.includes('int.')) {
    return 'integration';
  }
  
  return 'unit';
}

function displayVerificationResults(result: any) {
  console.log(`   🏆 総合評価: ${result.passed ? '✅ PASS' : '❌ FAIL'}`);
  
  console.log('\n   📋 個別検証結果:');
  result.results.forEach((check: any) => {
    const status = check.passed ? '✅' : '❌';
    const errors = check.errors ? ` (${check.errors.length} errors)` : '';
    const warnings = check.warnings ? ` (${check.warnings.length} warnings)` : '';
    
    console.log(`     ${status} ${check.type.toUpperCase()}${errors}${warnings}`);
  });

  console.log('\n   📊 カバレッジレポート:');
  console.log(`     📈 Line Coverage: ${result.coverage.line}%`);
  console.log(`     🌿 Branch Coverage: ${result.coverage.branch}%`);
  console.log(`     🔧 Function Coverage: ${result.coverage.function}%`);
  console.log(`     📝 Statement Coverage: ${result.coverage.statement}%`);

  console.log('\n   🎯 品質メトリクス:');
  console.log(`     🔄 Complexity: ${result.metrics.complexity}/10`);
  console.log(`     🛠️ Maintainability: ${result.metrics.maintainability}/100`);
  console.log(`     🔒 Security: ${result.metrics.security}/100`);
  console.log(`     ⚡ Performance: ${result.metrics.performance}/100`);
  console.log(`     🧪 Testability: ${result.metrics.testability}/100`);

  if (result.issues.length > 0) {
    console.log('\n   ⚠️ 検出された問題:');
    result.issues.slice(0, 5).forEach((issue: any, index: number) => {
      console.log(`     ${index + 1}. [${issue.severity.toUpperCase()}] ${issue.message}`);
    });
    
    if (result.issues.length > 5) {
      console.log(`     ... および ${result.issues.length - 5} 件の追加問題`);
    }
  }
}

async function generateDetailedReport(result: any, projectPath: string) {
  const reportData = {
    timestamp: new Date().toISOString(),
    projectPath,
    framework: 'ae-framework Verify Agent v1.0',
    summary: {
      overall: result.passed ? 'PASS' : 'FAIL',
      totalChecks: result.results.length,
      passedChecks: result.results.filter((r: any) => r.passed).length,
      failedChecks: result.results.filter((r: any) => !r.passed).length
    },
    coverage: result.coverage,
    metrics: result.metrics,
    traceability: result.traceability,
    issues: result.issues,
    suggestions: result.suggestions,
    detailedResults: result.results
  };

  const reportPath = path.join(projectPath, 'VERIFICATION_REPORT.json');
  writeFileSync(reportPath, JSON.stringify(reportData, null, 2));
  
  console.log(`   📄 詳細レポート保存: ${reportPath}`);

  // Markdownレポートも生成
  const markdownReport = generateMarkdownReport(reportData);
  const markdownPath = path.join(projectPath, 'VERIFICATION_REPORT.md');
  writeFileSync(markdownPath, markdownReport);
  
  console.log(`   📝 Markdownレポート保存: ${markdownPath}`);
}

function generateMarkdownReport(reportData: any): string {
  return `# E2E暗号化チャットアプリケーション - 品質検証レポート

**検証日時**: ${reportData.timestamp}
**検証フレームワーク**: ${reportData.framework}

## エグゼクティブサマリー

- **総合評価**: ${reportData.summary.overall === 'PASS' ? '✅ PASS' : '❌ FAIL'}
- **総検証項目**: ${reportData.summary.totalChecks}
- **成功**: ${reportData.summary.passedChecks}
- **失敗**: ${reportData.summary.failedChecks}

## カバレッジレポート

| メトリクス | 値 | 目標 | 状態 |
|-----------|-----|------|------|
| Line Coverage | ${reportData.coverage.line}% | 80% | ${reportData.coverage.line >= 80 ? '✅' : '❌'} |
| Branch Coverage | ${reportData.coverage.branch}% | 80% | ${reportData.coverage.branch >= 80 ? '✅' : '❌'} |
| Function Coverage | ${reportData.coverage.function}% | 80% | ${reportData.coverage.function >= 80 ? '✅' : '❌'} |
| Statement Coverage | ${reportData.coverage.statement}% | 80% | ${reportData.coverage.statement >= 80 ? '✅' : '❌'} |

## 品質メトリクス

| メトリクス | 値 | 評価 |
|-----------|-----|------|
| 循環的複雑度 | ${reportData.metrics.complexity} | ${reportData.metrics.complexity <= 10 ? '良好' : '要改善'} |
| 保守性指数 | ${reportData.metrics.maintainability} | ${reportData.metrics.maintainability >= 80 ? '良好' : '要改善'} |
| セキュリティ評価 | ${reportData.metrics.security} | ${reportData.metrics.security >= 90 ? '優秀' : reportData.metrics.security >= 80 ? '良好' : '要改善'} |
| パフォーマンス評価 | ${reportData.metrics.performance} | ${reportData.metrics.performance >= 90 ? '優秀' : reportData.metrics.performance >= 80 ? '良好' : '要改善'} |

## 検証結果詳細

${reportData.detailedResults.map((check: any) => `
### ${check.type.toUpperCase()}
- **結果**: ${check.passed ? '✅ PASS' : '❌ FAIL'}
${check.errors ? `- **エラー**: ${check.errors.length}件\n${check.errors.map((e: string) => `  - ${e}`).join('\n')}` : ''}
${check.warnings ? `- **警告**: ${check.warnings.length}件\n${check.warnings.map((w: string) => `  - ${w}`).join('\n')}` : ''}
`).join('')}

## 推奨改善事項

${reportData.suggestions.map((suggestion: string, index: number) => `${index + 1}. ${suggestion}`).join('\n')}

## トレーサビリティ

- **要件カバレッジ**: ${reportData.traceability.coverage}%
- **要件数**: ${reportData.traceability.requirements.length}
- **テスト数**: ${reportData.traceability.tests.length}
- **コードファイル数**: ${reportData.traceability.code.length}

---

**レポート生成**: ae-framework Verify Agent
**最終更新**: ${reportData.timestamp}
`;
}

function evaluateQualityGates(result: any) {
  const gates = [
    {
      name: 'テストカバレッジ',
      condition: result.coverage.line >= 80 && result.coverage.branch >= 80,
      description: 'ライン・ブランチカバレッジ ≥ 80%'
    },
    {
      name: 'セキュリティ',
      condition: result.metrics.security >= 90,
      description: 'セキュリティ評価 ≥ 90'
    },
    {
      name: 'コード品質',
      condition: result.metrics.complexity <= 10 && result.metrics.maintainability >= 80,
      description: '複雑度 ≤ 10 かつ 保守性 ≥ 80'
    },
    {
      name: 'テスト成功',
      condition: result.results.find((r: any) => r.type === 'tests')?.passed || false,
      description: 'すべてのテストが成功'
    }
  ];

  gates.forEach(gate => {
    const status = gate.condition ? '✅ PASS' : '❌ FAIL';
    console.log(`   ${status} ${gate.name}: ${gate.description}`);
  });

  const overallGate = gates.every(gate => gate.condition);
  console.log(`\n   🏆 品質ゲート総合評価: ${overallGate ? '✅ PASS' : '❌ FAIL'}`);
}

// スクリプト実行
runComprehensiveVerification().catch(console.error);