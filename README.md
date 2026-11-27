<p align="center"><img src="web/logo.svg" width="64" alt="LeanDuet"></p>
<h1 align="center">LeanDuet</h1>
<p align="center"><a href="https://github.com/Liangebra/leanduet/actions/workflows/ci.yml"><img alt="Tests" src="https://img.shields.io/github/actions/workflow/status/Liangebra/leanduet/ci.yml?branch=main&style=flat-square"></a> <a href="LICENSE"><img alt="MIT" src="https://img.shields.io/badge/license-MIT-blue?style=flat-square"></a></p>
<p align="center"><a href="README.md">English</a> · <a href="README.zh-CN.md">简体中文</a> · <a href="README.ja.md">日本語</a></p>

<p align="center">An open-source workbench for mathematical proofs.</p>
<p align="center"><a href="https://liangebra.github.io/leanduet/">Try the editor</a> · <a href="docs/RESEARCH.md">Research</a> · <a href="https://liangebra.github.io/leanduet/community.html#en">Community</a> · <a href="https://github.com/Liangebra/leanduet/discussions">Discussions</a></p>

---

### Install

Requires Python 3.10+. For proof checking, install [Lean 4](https://lean-lang.org/install/) with elan.

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

Open [localhost:8765](http://127.0.0.1:8765). No Node.js, database or AI key is needed to run the editor.

To use an existing Lean or Mathlib project, build its dependencies first, then run:

```sh
python server.py --project /path/to/project
```

The [online editor](https://liangebra.github.io/leanduet/) is a static demo. Run the local server for Lean verification, typed proof inspection and library search.

### Workbench

- Read a mathematical proof next to its Lean source, with native Lean completion (Ctrl+Space), or switch to a notebook layout.
- Inspect elaborated proof terms, local hypotheses and their types.
- Select a proof occurrence, search applicable rules, and review a checked replacement.
- Enter a supported LaTeX formula for typed proof completion, or compose controlled mathematical sentences with intermediate propositions inferred by Lean.
- Edit existential witnesses together with their dependent evidence.
- Interleave ordinary proof lines with multiple nested two-branch proofs for explicit disjunctions; branch-local assumptions stay scoped, and only shared results return to the parent.
- For conjunction and equivalence goals, bounded child-goal blocks prove each component or direction in an isolated scope. Existential goals accept an explicit, typed local witness and keep its property as a child obligation; open proof holes remain marked as obligations.
- A bounded “take an element satisfying …” request can retain both universal introduction and existential witness extraction when the goal and typed context support both. Choose a reading explicitly when the remaining draft cannot distinguish them; definitions and subtype coercions are not guessed.
- Preview a dependency-closed lemma and a checked refactoring that replaces the selected proof with its application. Multi-theorem editing remains experimental.
- Save locally, export Lean or a portable workspace, and read typed narratives in English, Chinese or Japanese, or import [community language packs](docs/LANGUAGE_PACKS.md).

- Explore freely in a locally saved, exportable mathematical notebook. Stage a selected formula only when you choose to formalize it. See [exploration design](docs/EXPLORATION.md).

### Why LeanDuet?

Lean verifies a proof term rather than its exposition. LeanDuet explores how mathematical exposition can be treated as an editable view of that structure, without discarding the author's choice of inference. Its core uses Lean's elaborator, type-directed library search and explicit structural checks, not an LLM as a verifier.

For the formal models and current experiments, see [research notes](docs/RESEARCH.md), [TMN](lean/TMN.lean) and [dependent contexts](lean/Dependent.lean).

### Status

LeanDuet is an early research prototype. It handles a restricted single-theorem source format. Natural-language editing uses a controlled grammar; unrestricted prose, arbitrary inductive case analysis, full-project LSP, universe-polymorphic export and source-preserving semantic edits remain open. The local service is not a sandbox: run trusted Lean code only. AI and Informath are optional; see [configuration](docs/CONFIGURATION.md).

### Contributing

Proof examples, mathematical vocabulary, type-theoretic models, tests and editor improvements are welcome.

[Contribution guide](CONTRIBUTING.md) · [Good first issues](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) · [Roadmap](docs/ROADMAP.md)

MIT · Independent project, not affiliated with Lean or Mathlib.
