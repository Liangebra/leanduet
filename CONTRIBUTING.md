# Contributing to LeanDuet

A mathematical proof is more than the fact that its conclusion is true. LeanDuet is an early research workbench for exploring how exposition, formal proof structure and local editing can coexist. We welcome disagreement, small reproducible counterexamples, and contributions from mathematicians who do not write software.

## Start here

| Interest | First contribution |
| --- | --- |
| Mathematics / teaching | [Supply an aligned proof example](https://github.com/Liangebra/leanduet/issues/2) or a [refactoring counterexample](https://github.com/Liangebra/leanduet/issues/9). |
| Languages | [Write a community language pack](https://github.com/Liangebra/leanduet/issues/8); see [schema](docs/LANGUAGE_PACKS.md). |
| Type theory / PL | Discuss [proof preservation](https://github.com/Liangebra/leanduet/issues/7) or [substitution and semantic interpretation](https://github.com/Liangebra/leanduet/issues/10). |
| Lean metaprogramming | [Native InfoTree and source alignment](https://github.com/Liangebra/leanduet/issues/1). |
| Engineering / usability | [Installation and workflow testing](https://github.com/Liangebra/leanduet/issues/6), [math rendering](https://github.com/Liangebra/leanduet/issues/3). |

Use [GitHub Discussions](https://github.com/Liangebra/leanduet/discussions) for exploratory conversations; use issues for reproducible bugs, focused research questions and actionable work. Read the [research agenda](docs/COMMUNITY.md) before starting a substantial redesign.

## A mathematical contribution without code

1. Choose a short proof you understand, ideally from algebra, analysis, topology or a dependent-type construction.
2. Supply a compiling Lean source (imports and toolchain), or clearly mark a proposed informal example as not yet formalized.
3. Explain the mathematics in your own words, identify its main inference and relevant hypotheses, and point out what a mechanical translation misses.
4. If proposing an edit, specify what must remain unchanged and what may change. A counterexample to our assumptions is welcome.

## Development

Fork and clone the repository, install the pinned Lean toolchain using elan, and run `python server.py`. Use trusted source only. No public sandbox is provided.

```sh
node --test tests/*.test.mjs
python -m unittest discover -s tests -p 'test_*.py'
lean lean/TMN.lean
lean lean/Dependent.lean
lean lean/Scoped.lean
python tests/semantic_integration.py
python tests/ir_integration.py
```

The browser and Mathlib jobs in [CI](.github/workflows/ci.yml) and [Mathlib CI](.github/workflows/mathlib.yml) provide additional reproducible checks. Tests involving Lean require a working toolchain. Run only the applicable tests and report any that could not run.

For a substantial change, discuss its mathematical or engineering intent and acceptance criteria in an issue before opening a PR. Include a minimal example, expected behavior, regression test, and the exact validation environment.

## Research integrity

- Distinguish a correct proof from a faithful explanation or structural refactoring. Proof irrelevance does not establish narrative equivalence.
- Do not hide unresolved proof obligations, weaken theorem statements, or discard edits. Mark unsupported constructs explicitly.
- Cite relevant papers and upstream code, respect licenses, and disclose substantial AI assistance. Human review is expected.
- Be respectful; critique arguments, not people. Contributions are under the MIT license.

See [the public contribution page](https://liangebra.github.io/leanduet/community.html) and [roadmap](docs/ROADMAP.md).
