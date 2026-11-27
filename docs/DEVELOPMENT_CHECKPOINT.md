# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Active work

The reviewed base is main commit `4f9f925` (PR #29). PR [#22](https://github.com/Liangebra/leanduet/pull/22) is merged; its physical source addresses, residual-goal checks, and expired local-name handling are in the base. PR [#29](https://github.com/Liangebra/leanduet/pull/29) is also merged. Its full Tests run and Mathlib-specific workflow passed; the Mathlib case generates and compiles an `IsCompact.image` candidate and checks dependent context closure.

The current source change composes supported ordinary inference lines with
multiple explicit binary-disjunction blocks, both at the theorem level and
inside a branch. A linear prefix is evaluated in continuation mode, then its
introduced declarations extend the lexical proof scope before the next case
block is compiled. Case results return to their parent scope; branch-local
facts expire. Physical line offsets are carried through the nested parser.
An unresolved prefix remains visible in the graph and keeps the whole draft
incomplete, even if later blocks remain structurally useful.

This continues stage 2 of the original eight-stage order and supplies a real
scope/control-flow requirement for stages 3, 6, and 7. It does not add general
prose parsing, arbitrary inductive elimination, or branch-level caching.

## Checked local state

- Node suite: 205 tests passed.
- Python unit suite: 17 tests passed.
- Python syntax compilation and `git diff --check`: passed.
- The Lean executable is not installed in this workspace. The updated
  `tests/interpret_integration.py` contains two generated sequence theorems
  (top-level interleaving and a local prefix inside a nested branch), while
  `tests/browser_smoke.py` exercises that sequence in the natural-draft editor.
  GitHub CI must compile and interact with them before this work can merge.
- `tests/draft-benchmark.mjs` checked incremental/cold structural equality
  across 160 samples per case, after 24 warmups, on Node v24.22.3 / Linux x64.
  Current medians/P95 (ms): 16-line cold 0.193/0.809; exact replay
  1.580/5.810; final-premise edit 1.214/1.858; dependency edit 1.318/3.136;
  eight-level case draft 6.725/10.778; two-case interleaving cold
  2.269/3.136; interleaving replay/terminal edit 2.356/3.653. This synthetic
  run shows no speedup claim: the warm path is not faster here, and nested
  cases report zero reused rows.

## Semantic boundaries

Case analysis remains an explicit binary `Or` operation, bounded to eight
nested splits and 64 nonblank lines per parsed block. Ordinary draft segments
remain limited to the existing controlled grammar and 16 inference lines.
The structural `complete` flag means only that the bounded program can be
rendered; it does not imply Lean elaboration or semantic fidelity. Formula
matching is conservative surface structure, not Lean definitional equality.
Scope IDs and physical line IDs are revision-local, and nested case bodies
are recomputed after edits.

## Next dependency-ready tasks

1. Submit the scope-sequence change as a separate PR and require Lean's
   generated-term integration plus browser smoke tests to pass.
2. Build the next proof operation around explicit child goals and closure
   conditions (first conjunction introduction), without adding classical
   reasoning or allowing local witnesses to escape their scopes.
3. Add structure-level candidates for phrases such as “take an element
   satisfying …”; preserve universal introduction, witness extraction,
   definition, and open existence as distinct possibilities.
4. Revisit branch-level incremental reuse only with cold-result comparison;
   the current benchmark establishes a baseline, not a performance target.

The aligned corpus now includes predicate-set operations and the Mathlib
compact-image example. The next stage-8 expansion should add a small number of
reviewed analysis or linear-algebra proofs with source language, expected
structure, generated Lean, and independent compilation.
