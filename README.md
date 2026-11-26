# LeanDuet

**Two languages, one proof.** Think in mathematics. Verify in Lean.

> Experimental v0.2 — a local Web workbench for linked mathematical narratives and Lean 4 proofs. Not a universal autoformalizer or a verified natural-language translator.

## Quick start

Install Python 3.10+ and optionally [Lean 4 via elan](https://lean-lang.org/install/). No Node.js or database is required for running the editor.

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

Open <http://127.0.0.1:8765>. Choose an example, edit either panel and click Sync (or opt into auto-sync). Click a reading-view step to locate it in Lean. Check in Lean invokes the local toolchain. Open and export individual .lean files.

Use an existing trusted Lake project with built dependencies:

```sh
python server.py --project /absolute/path/to/project
```

## Example

```lean
theorem nested (P : Prop) (h : P) : P ∧ P := by
  have h' : P := by
    exact h
  exact ⟨h', h⟩
```

The left panel uses a reversible controlled grammar: a JSON-quoted Lean fragment, prefixed by a readable label and its indentation. It preserves nested lines and blank lines; opaque tactics stay opaque. The reading view is more readable but not yet a mathematical-paper narrative. Indentation parents are lexical, not elaborated goal dependencies.

## What is implemented

- Single-declaration Lean ↔ controlled prose with exact LF round trips.
- Nested indentation mapping; linked source navigation; basic KaTeX rendering (CDN, plain-text fallback).
- Optional auto-sync, explicit conflict rejection and per-side revert; theorem header/import preservation on sync.
- Local Lean CLI check, .lean import/export, stale-check invalidation.
- Optional AI proposals in both directions, explicitly unverified and separate from synchronized prose.

## Optional AI

Set LEANDUET_AI_URL (full OpenAI-compatible chat-completions URL), LEANDUET_AI_MODEL, and optionally LEANDUET_AI_KEY in your environment. For example, a local Ollama endpoint may use http://localhost:11434/v1/chat/completions. Requests require explicit confirmation in the UI and send the proof to your chosen provider. No AI provider is necessary for the deterministic editor.

## Trust boundary

Run trusted code only: Lean imports, macros and tactics can execute code as your user. The server is not a sandbox; never expose it publicly. A Lean pass is not proof of informal/Lean semantic alignment, and the sorry check is not an axiom audit. Review AI code before running it. Only single-line theorem headers and space-indented proof bodies are supported; no whole-project parsing or block comments. Desktop and VS Code clients are planned, not shipped.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md), [the IR design](docs/PROOF_IR.md), and [the roadmap](docs/ROADMAP.md). Examples that expose failures are especially welcome.

```sh
node --test tests/core.test.mjs
python -m unittest discover -s tests
lean examples/Compose.lean
```

The release is experimental; real Lean and browser integration must be checked in a suitable environment. See [launch plan](docs/LAUNCH.md). Independent project, not endorsed by Lean or Mathlib. MIT; initial implementation assisted by ChatGPT.
