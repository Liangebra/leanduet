# Roadmap

## Stable prototype

- Single-theorem workbench, controlled syntax and source-linked reading.
- Native Lean completion, bounded library search, checked local edits and formula-only proof sequences.
- Community-importable mathematical language packs.
- Checked dependency-closed lemma abstraction and two-theorem factoring previews.
- Scope-indexed substitution laws and native judgment encoding/decoding with fresh-context round-trip checks.
- Experimental binary disjunction elimination, named local-lemma subproofs, and bounded conjunction/equivalence subgoals use nested, isolated scopes. Existential construction is limited to an explicit typed local witness. Classical reductio is available only as an explicit named operation; arbitrary inductive case analysis remains open.

## Experimental track

- Multi-theorem document inventory, direct/transitive references, native declaration ranges and checked single-declaration edits. These are under integration validation and not yet part of the stable workbench.

## Research priorities

- [Faithful proof presentations](https://github.com/Liangebra/leanduet/issues/7): define the right structural invariants.
- [Refactoring corpus](https://github.com/Liangebra/leanduet/issues/9): dependent types, Mathlib examples and counterexamples.
- [Typed interpretation and substitution](https://github.com/Liangebra/leanduet/issues/10): connect scope laws to actual IR.
- [InfoTree and source alignment](https://github.com/Liangebra/leanduet/issues/1): stable semantic source positions and incremental edits.
- Universe-polymorphic export, project-level LSP and richer mathematical narration.
- Community language resources, accessibility, packaging and interoperability.

No fixed release dates. Non-goals: claims of arbitrary natural-language equivalence, hard-theorem solving as the primary product, or public unsandboxed Lean execution.

See [community agenda](COMMUNITY.md) and [semantic IR design](SEMANTIC_IR.md).
