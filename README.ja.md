<p align="center"><img src="web/logo.svg" width="64" alt="LeanDuet"></p>
<h1 align="center">LeanDuet</h1>
<p align="center"><a href="https://github.com/Liangebra/leanduet/actions/workflows/ci.yml"><img alt="Tests" src="https://img.shields.io/github/actions/workflow/status/Liangebra/leanduet/ci.yml?branch=main&style=flat-square"></a> <a href="LICENSE"><img alt="MIT" src="https://img.shields.io/badge/license-MIT-blue?style=flat-square"></a></p>
<p align="center"><a href="README.md">English</a> · <a href="README.zh-CN.md">简体中文</a> · <a href="README.ja.md">日本語</a></p>

<p align="center">数学の証明のためのオープンソース・ワークベンチ。</p>
<p align="center"><a href="https://liangebra.github.io/leanduet/">エディターを試す</a> · <a href="docs/RESEARCH.md">研究資料</a> · <a href="https://liangebra.github.io/leanduet/community.html#ja">コミュニティ</a> · <a href="https://github.com/Liangebra/leanduet/discussions">Discussions</a></p>

---

### インストール

Python 3.10 以上が必要です。証明を検査するには、elan で [Lean 4](https://lean-lang.org/install/) を導入してください。

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

[localhost:8765](http://127.0.0.1:8765) を開きます。基本機能に Node.js、データベース、AI の API キーは不要です。

既存の Lean / Mathlib プロジェクトを利用する場合は、依存関係をビルドしてから実行します。

```sh
python server.py --project /path/to/project
```

オンライン版は静的なデモです。Lean による検査や定理検索はローカルサーバーで行います。

### ワークベンチ

- 数学的な証明と Lean ソースを並べて読む。ノートブック形式にも切り替え可能。
- elaboration 後の証明項、局所仮定とその型を調べる。
- 推論箇所を選択し、適用可能な定理を検索して検査済みの候補を確認する。
- 制御された数学的記述を組み合わせ、中間命題の型を Lean で推論する。
- 存在証明の証人と依存する証明義務をまとめて編集する。
- ローカル保存、Lean ファイルと作業状態のエクスポート。英語、中国語、日本語の型に基づく説明。

- 自由な探索ノートに予想、反例、未完成の議論を記録し、必要な数式だけを形式的な検査に渡せます。

### なぜ LeanDuet なのか

Lean が検査するのは証明項であり、数学的な説明文そのものではありません。LeanDuet は、その証明構造を編集可能な数学的記述として提示し、推論の選択を保持することを目指します。型推論、定理検索、構造の検査は Lean が担います。

[研究資料](docs/RESEARCH.md)、[TMN](lean/TMN.lean)、[依存文脈](lean/Dependent.lean) を参照してください。

### 開発状況

研究用の初期プロトタイプです。単一の定理を含む制限付きソースと制御言語に対応します。自由な自然言語、完全な LSP、宇宙多相な定理の出力、元のソースを保持する編集は今後の課題です。ローカルサーバーはサンドボックスではありません。信頼できる Lean コードのみ実行してください。AI と Informath はオプションです。[設定](docs/CONFIGURATION.md) を参照してください。

### コントリビューション

証明例、数学用語、形式モデル、テスト、エディターの改善を歓迎します。

[貢献ガイド](CONTRIBUTING.md) · [初心者向け Issue](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) · [ロードマップ](docs/ROADMAP.md)

MIT · Lean / Mathlib の公式プロジェクトではありません。
