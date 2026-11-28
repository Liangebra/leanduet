# Semantic intermediate language

## Separate representations

LeanDuet currently has several representations, not a single completed bidirectional IR:

- lexical source IR: exact source fragments and editing metadata;
- elaborated occurrence tree: Lean terms, local contexts, types, paths and direct/indirect dependencies;
- surface formula AST and controlled proof-chain syntax: parsed input before elaboration;
- TMN / Dependent / Scoped Lean models: mathematical specifications of supported operations.

Do not conflate these. The bounded browser-to-ScopedSemantics projection below is a first typed fragment and test bridge; it is not a completed bidirectional IR. The wider integration target remains a versioned semantic IR whose occurrence identity is distinct from definitional equality and which retains source provenance. Language packs are concrete syntaxes, not extensions to the Lean kernel.

## Categorical basis

1. Fiore, Plotkin, Turi, Abstract Syntax and Variable Binding, LICS 1999: https://lics.siglog.org/1999/FiorePlotkinTuri-AbstractSyntaxandVa.html . Scope-indexed syntax with renaming/substitution and initial-algebra semantics.
2. Ahrens, Hirschowitz, Lafont, Maggesi, High-Level Signatures and Initial Semantics, CSL 2018: https://doi.org/10.4230/LIPIcs.CSL.2018.4 . Extensible signatures compatible with substitution.
3. Dybjer, Internal Type Theory, 1996: https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf . Contexts and substitutions, dependent families and comprehension.
4. Ranta, Grammatical Framework, JFP 2004: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/grammatical-framework/09C4B3F43447ADDB0F632C64F195BC9C . One abstract syntax, multiple concrete grammars.
5. Aarne Ranta, Symbolic Informalization, 2026 preprint: https://arxiv.org/abs/2606.16893 . Dedukti/GF interlingual architecture.

## Implemented scope model

lean/Scoped.lean defines Term n with Fin n variables and binders whose bodies are in Term (n+1). Renaming lifts under binders; simultaneous substitution shifts inserted terms to avoid capture. The model states renaming identity/composition and identity substitution. The concrete families model defines reindexing, its identity/composition and the projection/eta equations for dependent context extension. These are small scope and context laws, not an initiality theorem, complete CwF formalization, or full Lean calculus.

The browser formula parser also produces a canonical scoped view using de Bruijn indices; it retains original names in the surface AST for display and source output. Alpha-equivalent bound names produce identical scoped views, while free names remain unresolved until Lean. The built-in unary spellings `Not P` and `¬ P` share one scoped form; this is a syntax alias, not general definitional equality. The general JS canonicalizer is not proved equivalent to the Lean model; the partial browser projection below is checked only on its stated fragment.

`lean/Scoped.lean` also defines a separate intrinsically typed fragment for
natural-number expressions and first-order propositions with equality,
conjunction, implication, and universal quantification over `Nat`. Its Lean
denotation is preserved by simultaneous capture-avoiding substitution; a
regression example substitutes through a universal binder. The typed syntax
erases into the generic `Scoped.Term`, and a second theorem proves that this
map commutes with substitution. This is an initial mathematical checkpoint
for Issue #10, but it is not a serialization or interpretation of the browser
AST or arbitrary Lean `Expr`. It excludes dependent object domains, general
predicates, constants, partial syntax and the full Lean type system. CI
compiles the model with the existing `lean/Scoped.lean` check.


## Browser formula projection to the typed scoped fragment

The browser exports `toScopedSemantics`, a partial structural map from a
closed surface formula to versioned JSON with an explicit context size and
de Bruijn indices. It accepts only explicit Nat binders, bound Nat variables,
zero, addition, equality, conjunction, implication, truth, and falsity. An
unannotated binder, free identifier or predicate, nonzero numeral, existential
or other unsupported operator returns a coded `ScopedSemanticsError`; the
projection does not infer a domain or declaration identity.

The integration check independently lowers the returned versioned nodes into
`LeanDuet.ScopedSemantics.Formula` and the browser's original scoped AST into
generic `LeanDuet.Scoped.Term`. Lean checks erasure equality and that the
typed fragment's denotation is definitionally equivalent to the browser
renderer on nested binders, alpha-renaming, same-name shadowing, arithmetic,
connectives, truth, and falsity. This is a one-way, closed-formula regression
bridge. It is not a general decoder, not a Lean Expr codec, and not a
natural-language or proof-route correspondence.

## Explicit local Nat contexts

A separate `toScopedSemanticsInContext` projection accepts an explicit finite
context of records `{id, name, type: "Nat"}`. The opaque stable `id` is kept
separate from the display name. Free names resolve only when exactly one
context record has that name; an unresolved or duplicate name is an error.
The context list is ordered oldest-to-newest, so the newest context object has
index 0 and every enclosing universal binder shifts context indices outward.
A formula binder shadows a context display name through the parser's de Bruijn
scope, without changing the context object's identity.

This remains a partial structural projection. It does not resolve arbitrary
Lean declarations, proposition-valued local assumptions, dependent types,
subtypes, or declaration renames by itself. A caller must update the context
record while retaining its id; this adapter does not infer cross-edit identity.
The projection's emitted context indices are checked against Lean's
`ScopedSemantics.denote` using an explicit environment, including a binder
that shadows a context name. Browser smoke also loads and calls the module
through the local HTTP server; it is not yet exposed as an interactive editor
control.

The Lean integration also applies `substFormula` to formulas emitted by this
projection and checks two concrete commuting cases: replacing the older of
two Nat objects while retaining the newer one, and replacing an outer object
under a universal binder without capturing the bound variable. In both cases
the substituted serialized syntax is definitionally the projection of the
corresponding updated formula, and the existing `denote_subst` theorem applies
to those emitted terms. These regressions exercise concrete inputs; they do
not prove the JavaScript projection preserves substitution for all formulas.

## Integration plan

Extend the closed Nat/Prop projection to explicitly typed local contexts and stable object identities. Then connect native Expr export with explicit binding identity and universe data. Define a type-preserving elaboration relation from surface syntax, retaining alternative parses if not unique. A local edit becomes a partial context morphism and checked replacement, preserving the surrounding proof complement. Establish substitution composition and then a theorem connecting the actual serialized representation to its Lean interpretation. Only after this link should we claim end-to-end semantic correctness.

Regex is useful for lexical tokens and finite controlled phrase boundaries; a recursive parser is needed for nested formulas and binders. Plain LaTeX does not uniquely determine mathematical semantics; explicit typed annotations, context and user disambiguation are necessary. Lean LSP identifier completion and bounded proof search are complementary, not the same operation.

The controlled chain also admits explicit proof holes: `Establish h : $P$ | ?` and `Conclude | ?`. These lower to Lean `exact?` calls, not `sorry`. Every completed candidate is subject to the existing rebuilt-proof and structural checks, including rejection of references to the original theorem. Failure to solve a hole is an ordinary elaboration failure. No completeness or deterministic proof choice is claimed.

## Composition laws

Scoped.lean now also states mixed renaming/substitution equations and associativity of simultaneous substitution. Substitution arrows n → m are Fin n → Term m; their composition is substitution of the second arrow into the first. The direction is that of variable assignments (opposite to context maps Δ → Γ). Identity and associativity are stated for these arrows. This is the finite-context relative Kleisli construction for the scope syntax, not a claim of a typed category of all Lean terms or an initiality proof. CI checks these Lean proofs.

## Native judgment schema (version 1)

The on-demand #duet_ir command and /api/ir endpoint serialize the selected Lean judgment Γ ⊢ t : A. Context entries preserve declaration order, numeric local slots, structural names, binder mode, types and optional let values, including internal declarations. Terms use tagged arrays: bound (de Bruijn), local (slot), sort, const (structural name and universe instantiation), app, lambda, pi, let, nat, string, projection. Metadata is erased. Universe levels are structural; arbitrary-size literal naturals and numeric name components use decimal strings. An optional surface formula is elaborated as a proposition in the same local context and exported alongside its definitional equality result, not inferred from printed names. The browser validates constructor shape and lexical scope, not types. JSON is read-only, revision-local, and bounded; the encoder rejects unresolved metavariables and excessive depth/size. There is no external JSON import or source-provenance map yet. The native decoder is exercised internally in the original local context; see below. The source Lean environment remains necessary to interpret constants. This is the first bridge from the actual kernel representation, separate from the pedagogical occurrence tree and the surface AST.

### Formula-only proof sequences

The proof editor can switch to a formula-only surface syntax: one delimited LaTeX formula per line, optionally named for intermediate results. All earlier lines create typed proof holes; the last uses a `show` statement so that Lean must accept the proposition as the selected target. Generated intermediate names avoid supplied local names. The same structured steps and checked patch pipeline apply. No completeness or proof-choice guarantee is claimed.

### Initial natural-language set-theory fixture

The presentation formula grammar recognizes set union and intersection,
including `\cup` and `\cap`, at Lean core precedences 65 and 70. This keeps
`x ∈ A ∩ B` grouped as membership in the intersection. The aligned fixture in
`tests/fixtures/real-math-cases.json` pairs a Chinese proof sketch with its
selected goal, typed context and generated Lean declaration. It uses a small
predicate-set model with explicit `Membership` and `Inter` instances, so the
generated result compiles under the pinned Lean toolchain without another
Mathlib installation. This is a kernel-checked set argument, but it is not
evidence of broad Mathlib prose coverage; the topology example in
`tests/mathlib_integration.py` remains a separate adapter test.

In the commutativity fixture, the browser draft writes `And.intro hB hA`, while
the elaborated tree exposes the resulting conjunction as a constructor pair.
The integration test therefore aligns an actual projection node (`hx.right`)
and separately checks that the pair contains the two local results; it does not
assume that Lean's elaborated tree preserves the surface declaration spelling.

### Branch-local proof scopes

The natural draft accepts an explicit disjunction block, for example:

```text
分情况讨论 h，建立 hR : $R$
  左支 hp
    $R$ | f hp
  右支 hq
    $R$ | g hq
$R$ | hR
```

The source must be a uniquely named local declaration whose parsed type is a
binary disjunction. Nested blocks are parsed after removing the enclosing
branch indentation. Each arm is compiled in a forked proof scope with a
distinct local binding identity; sibling display names may coincide. Closing
an arm checks its common surface target, discharges local identities, and
returns only parent-context dependencies. The graph keeps both branch trees
and dependency sets, while the parent continuation refers to the case result.
An unfinished branch stays in the graph and prevents a complete Lean term
from being exported. If a parent continuation follows, the common result is
represented provisionally so later statements remain available in the graph
and carry an open dependency on that result. The continuation is never
rendered as an executable Lean term until the branch closes, and its final
surface proposition is still checked against the remaining goal. Branch-local
names remain unavailable after closure, including while another branch is
open.

This surface check is not Lean elaboration and does not decide arbitrary
typeclass or definitional-equality questions. The structured backend emits
nested `cases ... with` blocks for `Or`, then asks Lean to elaborate and trace
the parent result. Only that result is returned as a binding; branch-local
assumptions and intermediate declarations are not traced out of their scope.
The supported operation is binary disjunction elimination only, bounded to
eight nested splits and 64 nonblank surface lines. It does not provide general
inductive case analysis, contradiction, or unrestricted branching prose
parsing. Recomputing a case block is currently a full block evaluation;
branch-aware prefix caching remains future work.

At the top level and within a branch, supported ordinary inference lines may
now occur before, between, and after multiple case blocks. The evaluator
compiles each linear prefix as a continuation rather than prematurely treating
its last line as the theorem conclusion, extends the structured scope with
those local declarations, and then parses the next case block. The same
physical source-line addresses flow into the nested parser. If an earlier
linear segment contains an unresolved row, later case structure remains in the
graph but the combined draft stays incomplete. This composition does not
broaden the accepted sentence grammar, and nested case bodies are still
recomputed rather than incrementally reused.

### Named local-lemma return

The bounded draft accepts `local lemma h : $P$` (also `prove lemma` and
`局部引理` / `证明引理`) followed by an indented `proof` block. The lemma
statement is explicit, and the proof body runs in a child scope inheriting the
parent's object identities. Closing the block checks the child's declared
target, discharges child-local bindings, and returns only dependencies that
already existed in the parent together with the new proposition binding.
Sibling and enclosing proof scopes retain their own identities.

An unfinished proof keeps its claim and later parent rows in the graph as
open-dependent structure; it cannot export a Lean term. A structurally closed
body that uses an upstream open object remains a candidate with that dependency
marked open. The backend emits `have h : P := by ...` and its Lean check is
independent of browser closure. This operation requires an explicitly stated
lemma and supported child proof lines; it does not infer a useful lemma,
automatically choose a proof strategy, or establish informal fidelity. Nested
scope and source-size limits match the bounded goal operations. The whole
local-lemma block is currently recomputed after structural edits.

## Checked same-context round trip

The native decoder reconstructs all supported Expr constructors with exact structural names, universe levels, binder modes and local-slot identity. Each exported context type/value, selected term/type and optional formula is decoded in Lean, checked, compared with its original shape, and re-encoded to the identical JSON. The final decoded term must have a type definitionally equal to the decoded target. The returned roundTrip fields record these checks. This verifies individual exported judgments in their original context; it is not a general formal theorem, cross-project import, independent environment reconstruction, or a proof of the browser parser. No external JSON is executed or accepted by the API. The decoder rejects unknown constructors and out-of-scope slots. Encoding and round-trip checking share a bounded inspection budget.

## Fresh local-context verification

The checker now additionally discards the original local context and reconstructs the serialized telescope from scratch in the same Lean environment. Each declaration must be a type; let values must have the declared type. The decoder introduces fresh local identities, resolves the old numeric slots to these fresh variables and checks the reconstructed term and target. Abstracting both the original and rebuilt terms over their respective local variables must preserve shape (including the type). This is a fresh-context check, not an independent global environment import; the global constants and universe parameters still rely on the original Lean environment. Internal declaration flags are informational, not a complete serialization of Lean implementation-specific local-context metadata.

## Proof abstraction

The same ordered dependency closure used by the context inspector now supports a checked abstraction operation. Given Γ ⊢ t : P, retain the declarations referenced by t or P and close transitively through their types and let values. Wrap the term with lambda/let binders and the statement with Pi/let binders in reverse declaration order. Check the resulting closed judgment in an empty local context; reopen the binders to the original free-variable identities and require structural equality of both the selected term and proposition. For supported monomorphic imports-only documents, the preview is separately compiled as a standalone theorem, then the elaborated statement and proof shape are compared with the actual abstraction. Otherwise show a checked internal judgment with an explicit export limitation. This is a preview, not automatic refactoring or a theorem of minimal hypotheses. In particular, local definitions are not incorrectly generalized as unconstrained parameters, and proof irrelevance alone is not used as the structural comparison.

Regression fixtures include a genuinely local let built in MetaM, distinct assumptions of the same type, the universe-polymorphic export limitation, and the browser preview's no-source-mutation contract.

## Checked factoring preview

After a standalone lemma has been certified, a new structural operation replaces the selected occurrence by an application of that lemma. Arguments are actual local identities from the dependency closure; let declarations are not passed as parameters. The lemma body must match the exact abstraction, not just its proposition. The resulting theorem type is checked, then both declarations are compiled independently, and the elaborated result is compared to the expected single-occurrence replacement. The rest of the proof is therefore preserved modulo the existing shape equivalence (alpha names, metadata and let flags). The two-theorem document is a preview only: the current single-theorem editor cannot yet adopt it as an editable project. Universe-polymorphic factoring and arbitrary preludes remain unsupported.

The export printer now requests explicit binder types, universe levels, coercions, proof arguments and non-notation syntax for both extracted terms and statements; the independent shape check is unchanged. On a mismatch the expected and actual canonical expressions are reported.

## Proof-refactoring counterexample

`tests/mathlib/ProofRefactorCounterexamples.lean` gives two compiling Mathlib
proofs of the same compact-image proposition. Both contexts contain distinct
`h1 h2 : IsCompact s`, while the selected subterm is
`IsCompact.image h2 hf`. The dependency view must retain `h2` and exclude
`h1`, even though their types coincide. A second proof binds that subterm to
a local `imageProof`; its elaborated occurrence tree contains a let node.
The Mathlib integration check compiles both declarations, compares their
statement types, and checks the two dependency closures. This is a concrete
counterexample to selecting proof dependencies by proposition type or
treating source-level factoring as proof-shape preservation. It does not
establish a general source-to-proof alignment or minimality theorem.

The same fixture now adds a dependent existential witness in `Fin (n + 1)`.
The integration compiles direct and local-let versions, checks that the local
let's value is `x` and its type depends on `n`, and confirms that the
`Exists.intro` closure retains `h2`, the predicate and witness context while
excluding same-typed `h1`. This is one checked dependent example, not a
general proof of dependency minimality.

## Browser formula to native IR regression (Issue #10)

`tests/ir_integration.py` now drives the browser formula parser on nested
natural-number quantifiers, addition and equality. It checks the browser's
de Bruijn indices, emits a Lean theorem from the rendered formula, and uses
Lean's elaborator plus the native judgment round-trip checker to compare the
formula and theorem type. Cases cover distinct binder renaming and repeated
binder names in nested scopes; the latter must resolve to the innermost
binder. Native binder display names are erased before structural comparison,
while `matchesGoal` is still checked by Lean.

This is an executable regression on a narrow fragment. It does not prove that
the JavaScript parser implements `ScopedSemantics`, that all browser ASTs map
to native `Expr`, or that structural equality is general mathematical
equivalence. Free identifiers, dependent domains, partial formulas and other
unsupported grammar remain outside this test.
