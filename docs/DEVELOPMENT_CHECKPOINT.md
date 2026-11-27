# LeanDuet development checkpoint

Updated 2026-11-27 (Asia/Shanghai).

## Current mathematical focus

The current line of work extends the proof-scope foundation into small aligned
mathematics examples. The immediate corpus is set intersection over predicates
(`PredSet α := α → Prop`): projecting membership from an intersection and
reordering the two components. These examples exercise bounded quantifier
introduction, hypothesis introduction, local result identity, ordered
intermediate reasoning, and Lean's `And.left`, `And.right`, and `And.intro`.
They are deliberately small Lean-core models, not evidence that arbitrary set
theory prose or Mathlib proofs can already be translated.

The formula AST recognizes `\cap`/`\inter` and `\cup`/`\union`. Its parser
uses the Lean precedences for `+` and union (65), and `*` and intersection
(70), so mixed expressions preserve the parsed tree. This is syntax support;
it does not by itself add union reasoning rules.

## Merged foundation

- PR [#22](https://github.com/Liangebra/leanduet/pull/22), merge `0eaf7dd`:
  physical source addresses, residual-goal checking, and closed branch-local
  names.
- PR [#24](https://github.com/Liangebra/leanduet/pull/24), merge `c6bf9f4`:
  opt-in latency and incremental/full structural comparison benchmark.
- PR [#23](https://github.com/Liangebra/leanduet/pull/23), merge `83d0154`:
  open and nested disjunction branches retain parent continuations while local
  names remain scoped.
- PR [#25](https://github.com/Liangebra/leanduet/pull/25), merge `fcc66aa`:
  intuitionistic negation introduction leaves `False` as the remaining goal;
  it does not insert classical reasoning.

The original eight-stage order in `IMPLEMENTATION_ORDER.md` remains in force.
The next dependency-ready work is still stage 2: generalize goal/context
operations and subproof lifecycle beyond the current implication, quantifier,
existential, and explicit binary-case mechanisms. In parallel, retain the
current small corpus while stage 8 expands to genuine Mathlib examples.

## Validation and limits

Local verification passes: 190 Node tests, 17 Python unit tests, Python syntax
compilation, and the full `tests/interpret_integration.py` run under Lean 4.19.
That integration compiles both generated declarations and checks the extracted
Lean trees and local dependency closures. The first PR CI run caught a mistaken
assumption that `And.left hx` would remain textually named in Lean's tree; the
test now checks its actual projection form (`hx.left`) and constructor-pair
representation. The browser smoke test still awaits GitHub CI, because this
workspace does not have a Playwright browser installed.

The natural-language draft remains a bounded, rule-guided grammar, not
unrestricted prose parsing. A structural `complete` result means the draft has
the required shape and goal annotations; only the separate Lean check can
establish elaboration. Formula comparison is conservative surface structure
modulo bound-variable renaming, not Lean definitional equality. Case analysis
currently requires an explicit binary disjunction, is bounded to eight nested
splits and 64 nonblank source lines, and fully recomputes case bodies after an
edit.

No performance improvement is claimed for these syntax and corpus changes.
The existing opt-in benchmark is synthetic, bounded to the current draft
engine, and checks incremental/full result equality rather than enforcing a
speed threshold. One local rerun (Node v24.22.3, Linux x64, 24 warmups and 160
samples; median/P95 milliseconds) measured 0.211/0.538 for cold evaluation,
0.196/1.493 for exact replay, 0.185/0.458 for a final-premise edit,
0.196/0.453 for a local dependency edit, and 2.406/4.140 for 41 lines with
eight nested case levels. This is one synthetic environment and includes a
noisy replay tail; it is not a production latency claim. Nested case blocks
currently recompute their branch bodies.

## Open problems and next entry points

1. Generalize proof operations around child goals, local context extension,
   closure conditions, and returning a result to the parent; make witness
   escape rules explicit for all nested scopes.
2. Add structure-level ambiguity candidates for phrases that could introduce
   a universal variable, extract an existential witness, define an object, or
   leave an existence obligation. Preserve unsupported, underspecified,
   inconsistent, and budget-exhausted states separately.
3. Extend aligned examples from the current predicate-set model to actual
   Mathlib declarations, beginning with the existing compact-image topology
   integration and adding prose only where the current grammar can preserve
   the statement and proof path honestly.
4. Improve branch-level incremental reuse and continue comparing it against a
   full cold evaluation. Do not infer a speedup from code shape.
5. Clarify surface structural mismatches versus Lean definitional equality in
   diagnostics and candidate states.
