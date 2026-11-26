# Research and community agenda

LeanDuet asks how an informal mathematical argument can be treated as a structured, editable view of a formal proof. We are interested in what can be established rigorously and what must remain a matter of mathematical exposition.

## Open questions

**Preserving mathematical reasoning.** What is the right equivalence relation on proof presentations? Which differences are harmless, and which change the argument? [Discussion prompt #7](https://github.com/Liangebra/leanduet/issues/7).

**Abstraction and refactoring.** A local proof has an ordered dependent context. Can we identify its useful abstraction, preserve local definitions, and retain the surrounding proof? Please contribute small examples where pretty-printing, proof irrelevance, or type inference obscures this. [Corpus #9](https://github.com/Liangebra/leanduet/issues/9).

**Composition and interpretation.** We have a scope-indexed syntax with substitution laws and a separate native Lean judgment codec with checked instance-by-instance round trips. A general typed interpretation compatible with substitution remains a research goal. [Formalization #10](https://github.com/Liangebra/leanduet/issues/10).

**Concrete mathematical languages.** The surface grammar and language packs should represent the same mathematical structures, not force every language into literal English syntax. [Language packs #8](https://github.com/Liangebra/leanduet/issues/8).

## What counts as useful feedback?

A five-line counterexample with a clear explanation can be more valuable than a large feature request. Include the statement, formal or informal argument, relevant context, and what an editor should preserve. We also welcome feedback on accessibility and the reading workflow.

The stable main branch is a research prototype, not a universal formalizer. The experimental multi-declaration/refactoring branch is not advertised as released. See [semantic IR](SEMANTIC_IR.md), [research notes](RESEARCH.md), and [contributing](../CONTRIBUTING.md).

[Open a discussion](https://github.com/Liangebra/leanduet/discussions) · [Browse open tasks](https://github.com/Liangebra/leanduet/issues)
