<p align="center"><img src="web/logo.svg" width="92" alt="LeanDuet logo"></p>
<h1 align="center">LeanDuet</h1>
<p align="center"><strong>Two languages, one proof.</strong><br>Think in mathematics. Verify in Lean.</p>
<p align="center"><a href="https://github.com/Liangebra/leanduet/actions/workflows/ci.yml"><img alt="Tests" src="https://github.com/Liangebra/leanduet/actions/workflows/ci.yml/badge.svg"></a> <a href="LICENSE"><img alt="MIT License" src="https://img.shields.io/badge/license-MIT-blue"></a> <a href="https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22"><img alt="Contributions welcome" src="https://img.shields.io/badge/contributions-welcome-5267a8"></a></p>

LeanDuet is an experimental mathematical proof workbench. It explores how an informal mathematical argument and a Lean 4 proof can become linked, editable representations rather than unrelated documents.

**v0.4 development prototype** — not a universal autoformalizer, Lean LSP client, or certified natural-language translator.

## Try it locally

Install Python 3.10+; install [Lean 4 via elan](https://lean-lang.org/install/) if you want verification. No server subscription, Node.js, database, or AI key is required for the basic editor.

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

Open <http://127.0.0.1:8765>. Use `python3` or `py` if needed. On Windows, macOS and Linux, the same interface runs in your browser.

## A proof-oriented workspace

- Mathematical reading view, source-linked steps, outline, line numbers and diagnostics.
- Five authored examples with mathematical narratives and native MathML for simple expressions. An edited example falls back to explicitly labeled structural text, never stale exposition.
- Edit a linked guided sentence or formal step, or use the reversible controlled-text tab to synchronize in either direction. Optional auto-sync, conflict protection, explicit statement adoption, and per-side discard.
- Local autosave of both unsynchronized drafts and free-prose notes. Export a portable JSON workspace or a Lean file. Dark/light themes, reading focus mode and explicit new-proof creation.
- Optional AI explanation and Lean proposals from free prose; explicit review before applying. Local Lean CLI verification, separate from narrative fidelity.
- Browser-only [live demo](https://liangebra.github.io/leanduet/) on GitHub Pages. The static site has no Lean execution or AI backend; see [deployment instructions](docs/DEPLOY.md).

## Example

```lean
theorem compose_imp (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  have hq : Q := hpq hp
  exact hqr hq
```

In the reading view, assume P, obtain Q by the first implication, and conclude R using the second. Select a step to find its corresponding Lean line.

## Using an existing Lean project

After building the project's dependencies, launch:

```sh
python server.py --project /absolute/path/to/project
```

The current parser handles **one theorem or lemma with a single-line or space-indented multiline header** and space-indented proof. It preserves opaque lines rather than pretending to understand them. No full-project parsing, LSP integration, or logical proof dependency extraction yet.

Optional AI: set `LEANDUET_AI_URL` (full OpenAI-compatible chat-completions endpoint), `LEANDUET_AI_MODEL`, and optionally `LEANDUET_AI_KEY`. A local Ollama-compatible endpoint may use `http://localhost:11434/v1/chat/completions`. Requests require consent; the proof and notes go to your configured provider.

## Type-theoretic research track

The Typed proof tab calls a local Lean metaprogram to inspect elaborated theorem terms, inferred types, binders and proof arguments. It is separate from the lexical editor. An optional Informath button invokes the independently installed upstream CLI. Set LEANDUET_INFORMATH_ROOT and optionally LEANDUET_INFORMATH_BIN; upstream needs a compatible Lean toolchain (see its own documentation). This integration has not yet been run against an installed upstream runtime.

The local Typed proof tab also offers a checked term-level replacement preview for monomorphic theorems: local elaboration, whole-proof checking, standalone recompile and definitional statement comparison precede explicit application. This can rewrite the surface header and tactic layout.

The experimental dependent track adds quantified inference, certified existential witnesses and equality transport in [lean/Dependent.lean](lean/Dependent.lean). The local inspector offers bounded one-argument applications and editable existential witnesses, subject to full dependent validation.

See [research references and reuse policy](docs/RESEARCH.md) and the small indexed natural-deduction calculus in [lean/TMN.lean](lean/TMN.lean). The calculus and extractor are included in CI; no claim of full Lean-to-natural-language reversibility.

## Trust and privacy

Run trusted Lean code only. Tactics, imports and macros can execute arbitrary code; the Python service is local-only and is **not a sandbox**. Lean success is not a proof of the correctness of prose or an axiom audit. Authored examples are source-bound, not formally certified. Free prose does not automatically become Lean unless an optional AI provider proposes a candidate. MathML renders a limited expression vocabulary; arbitrary LaTeX and semantic translation remain open work. Local autosave uses browser storage; export a workspace for backups.

## Help build it

We welcome mathematicians, Lean developers, PL researchers and interface designers. You can contribute a proof example **without writing application code**.

- [Good first issues](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
- [Contribution guide](CONTRIBUTING.md) · [Proof IR](docs/PROOF_IR.md) · [Roadmap](docs/ROADMAP.md)
- [Launch plan](docs/LAUNCH.md) · [Community and deployment checklist](docs/DEPLOY.md)

```sh
node --test tests/*.test.mjs
python -m unittest discover -s tests
lean examples/Compose.lean
```

CI also runs a real Chromium smoke test after installing Lean. Local tests require their respective tools; a configured CI badge is not a claim of successful execution.

MIT · Independent community project, not endorsed by Lean or Mathlib. Initial implementation assisted by ChatGPT.
