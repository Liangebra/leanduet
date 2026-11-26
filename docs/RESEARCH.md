# Research foundations and upstream reuse

## References
- Aarne Ranta, [Type theory and the informal language of mathematics](https://ncatlab.org/nlab/files/InfLang.pdf). Design motivation: typed objects, dependent binders, context-sensitive mathematical language.
- Aarne Ranta, [Symbolic Informalization: Fluent, Productive, Multilingual](https://arxiv.org/abs/2606.16893), 2026 preprint. [Informath](https://github.com/GrammaticalFramework/informath) separates formal interlingua (Dedukti) from grammatical realization (GF).
- Peter Koepke, [A Natural Language Formalization of Perfectoid Rings in Naproche](https://doi.org/10.4230/LIPIcs.ITP.2025.6), ITP 2025. [Naproche](https://github.com/naproche/naproche) demonstrates controlled mathematical language and proof obligations, but uses a first-order internal logic.
- [Contract Lenses: Reasoning about Bidirectional Programs via Calculation](https://doi.org/10.1017/S0956796823000059), JFP 33 e10 (2023). Adopt partial update contracts rather than claiming bijection of prose and Lean.

## What is reused
Informath is an optional external executable called via its documented CLI, not a copied implementation. Upstream informath.cabal declares BSD-3-Clause, but the repository root currently has no standalone license file; preserve attribution and confirm terms before vendoring any source. Upstream scripts/lean/README.md says Export.lean targets Lean 4.36; our pinned Lean 4.19 is not automatically compatible. Use an independently installed, compatible Informath runtime. We have not executed the upstream CLI in CI yet. Its Dedukti output is explicitly a reading-oriented translation, not a faithful kernel serialization. Naproche is GPL-3.0: cite and study, do not copy GPL code into MIT core without resolving licensing. No third-party source is vendored in this change.

## Mathematical core
lean/TMN.lean encodes a small propositional natural-deduction calculus as data indexed by a context and proposition, with compile : Derivation Γ P → Holds Γ → P. The Lean type checker verifies the implementation when CI compiles it. A typed context is a function from one derivation interface to another. This models substitution at a fixed interface, not general dependent substitution. The partial lens structure encodes GetPut and PutGet; pairLens is a concrete complement-preserving example, not yet a proof of the IDE's update algorithm.

lean/Extract.lean independently traverses an actual elaborated theorem value, opening lambda/let binders with local contexts and inspecting inferred types. Application nodes include named references and proof-argument children. The output intentionally omits nonproof arguments as child nodes, caps depth and branching, and keeps terms as pretty-printed strings. Do not treat it as lossless, nor as a logical dependency graph. A later implementation must serialize typed Expr with binding identity, universe levels, implicit arguments, and provenance, then align to InfoTree source ranges.

## Integration roadmap
1. Typed proof extraction and small calculus (this development batch).
2. Compare source and extracted proof with Informath exporter output, especially Mathlib constants and nested tactics.
3. Typed term reification, source-range mapping, binder hygiene and dependent substitution.
4. Define an editable grammar with checked proof obligations, prove lens laws for its supported fragment.
5. Add reviewed multilingual lexical entries; use GF/Informath when compatible. Avoid hallucinated theorem statements and silent proof changes.

## Reproducible upstream reference

Inspected Informath revision [9a1b6e1](https://github.com/GrammaticalFramework/informath/tree/9a1b6e10ddb8563cc2392e015957452f950a6f4c), including [exporter documentation](https://github.com/GrammaticalFramework/informath/blob/9a1b6e10ddb8563cc2392e015957452f950a6f4c/scripts/lean/README.md) and Cabal metadata. Its separate [Mathlib informalization](https://github.com/aarneranta/mathlib-informath) is a useful reference corpus; no license was reported by GitHub, so do not copy its data blindly.

The optional CLI adapter can set LEANDUET_INFORMATH_TOOLCHAIN independently of our native Lean toolchain. Project-mode Informath is explicitly rejected until its Lake integration is implemented. Mock tests check invocation only; the external executable is not installed in CI.

The typed viewer now also has a deterministic English/Chinese reading: lambda binders establish scope; applications emit proof-argument premises before the conclusion; a small lexicon recognizes exact core declaration names. Unknown terms are left explicit. This is a partial reading, not a certified natural-language view or a general translator.

## Scoped typed replacement (development)

The propositional calculus uses positional Slot values in Type rather than proof-irrelevant list-membership witnesses, and a syntactic one-hole context with explicit hole scope and target. Hole.plug and Hole.sound express a local substitution contract for the supported natural-deduction constructors.

The Lean Expr inspector attaches revision-local paths to proof nodes. The patch command opens local binders, elaborates a replacement against the exact local proposition, reconstructs the original expression along the path, and checks the rebuilt closed term against the original theorem type. It then pretty-prints a complete term-style candidate. The Python driver independently recompiles that candidate with the original imports and compares the new declaration type with the old by definitional equality in Lean. The original source is not modified until the user explicitly applies the preview. This preserves the statement's kernel type, not the original header spelling or tactic layout.

Scope is deliberately limited to one theorem with imports only and no universe parameters. Re-elaboration can fail and must not silently fall back to unverified source. This is an experimental term-level editing bridge, not yet a proof of semantic alignment or a source-preserving patcher. The formal Hole calculus and the Lean Expr reconstruction are not yet formally related.
