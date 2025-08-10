# ae-framework Implementation Records

このリポジトリは ae-framework を使用した実際の開発セッションの記録を保存し、フレームワーク改善のための分析データとして活用します。

## 保存されている実装記録

### [20250110-EncryptedChatApp](./implementations/20250110-EncryptedChatApp/)
- **日付**: 2025年1月10日
- **アプリケーション**: E2E暗号化チャットアプリケーション
- **技術**: Signal Protocol, Double Ratchet, X3DH, TypeScript, Fastify
- **主な問題**: TDD原則の違反、テスト未実行
- **学習事項**: フレームワーク改善提案に繋がった重要なケース

## 記録の構造

```
implementations/YYYYMMDD-ApplicationName/
├── README.md           # 開発セッション概要
├── ANALYSIS.md         # 問題点と改善提案
├── metrics.json        # 開発メトリクス
├── phases/            # フェーズ毎の成果物
│   ├── 1-intent/      # 要件定義
│   ├── 2-formal/      # 形式仕様
│   ├── 3-tests/       # テスト
│   ├── 4-code/        # 実装
│   ├── 5-verify/      # 検証
│   └── 6-operate/     # 運用
├── prompts/           # プロンプト履歴
└── violations/        # 違反記録
```

## 利用目的

1. **フレームワーク改善**: TDD違反パターンの分析
2. **ベストプラクティス抽出**: 成功/失敗パターンの文書化
3. **メトリクス分析**: 開発効率の測定

## 関連Issue

- [ae-framework改善提案](https://github.com/itdojp/ae-framework/issues/1)
- [実装記録保存ルール](https://github.com/itdojp/ae-examples/issues/2)