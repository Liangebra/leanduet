<p align="center"><img src="web/logo.svg" width="92" alt="LeanDuet ロゴ"></p>

# LeanDuet — 二つの言語、一つの証明

[English](README.md) · [简体中文](README.zh-CN.md) · **日本語** · [オンラインデモ](https://liangebra.github.io/leanduet/) · [プロジェクト紹介](https://liangebra.github.io/leanduet/about.html#ja)

LeanDuet は、数学者のための実験的なオープンソース証明ワークベンチです。自然な数学的記述と Lean 4 の形式証明を単なる翻訳対象ではなく、依存型理論に基づく共通の推論構造の、相互に関連した表現として扱うことを目指しています。

## 現在の機能

- 数学的な証明の閲覧、Lean ソースとの位置対応、編集と同期。ローカル保存、インポート・エクスポート、ライト／ダークテーマ。
- Lean の elaboration 後の証明項、型、局所文脈、存在証明の証人を抽出し、型に基づく説明を生成。
- 目標の型や制御された数学用語からライブラリの定理を検索。候補の局所編集は型検査、独立した再コンパイル、証明構造の一致検査を通過する必要があります。
- 存在命題の証人とその証明義務を一緒に編集。制御された複数ステップの推論文から候補項を生成。
- 互換性のある Mathlib プロジェクトを利用可能。コンパクト集合の連続像に関する `IsCompact.image` の統合テストは実際に成功しています。

## はじめに

Python 3.10 以上が必要です。証明を検査する場合は [elan](https://lean-lang.org/install/) で Lean を導入してください。基本的な編集には AI の API キーは不要です。

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

ブラウザで <http://127.0.0.1:8765> を開きます。ビルド済みの Lean プロジェクトを利用する場合：

```sh
python server.py --project /absolute/path/to/project
```

[オンラインデモ](https://liangebra.github.io/leanduet/) は静的な編集画面です。Lean、Mathlib、AI の実行機能はローカルサーバーで利用します。

## 研究の方向性

型付き数学的叙述、局所文脈、依存量化、等式による型の移送、部分的な双方向変換を研究しています。[TMN](lean/TMN.lean)、[依存型モデル](lean/Dependent.lean)、[研究資料](docs/RESEARCH.md) を参照してください。

現在は研究用プロトタイプです。単一の定理を含む制限付きのソースを対象とし、任意の自然言語を理解するものではありません。日本語の紹介と一部の制御語彙を提供しますが、エディター全体の日本語化は未完了です。すべての宇宙多相な定理や tactic の書式保持には対応していません。信頼できる Lean コードのみ実行してください。ローカルサーバーはサンドボックスではありません。Informath の実環境との接続は未検証です。

## コントリビューション

数学者、Lean 開発者、プログラミング言語研究者、UI デザイナーを歓迎します。数学的な証明例、用語集、翻訳の提供も重要な貢献です。

[貢献ガイド](CONTRIBUTING.md) · [初心者向け Issue](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) · [Discussions](https://github.com/Liangebra/leanduet/discussions) · [ロードマップ](docs/ROADMAP.md)

MIT ライセンス。Lean や Mathlib の公式プロジェクトではありません。
