# Semantic intermediate language

## Separate representations

LeanDuet currently has several representations, not a single completed bidirectional IR:

- lexical source IR: exact source fragments and editing metadata;
- elaborated occurrence tree: Lean terms, local contexts, types, paths and direct/indirect dependencies;
- surface formula AST and controlled proof-chain syntax: parsed input before elaboration;
- TMN / Dependent / Scoped Lean models: mathematical specifications of supported operations.

Do not conflate these. The next integration target is a versioned typed semantic IR whose occurrence identity is distinct from definitional equality and which retains source provenance. Language packs are concrete syntaxes, not extensions to the Lean kernel.

## Categorical basis

1. Fiore, Plotkin, Turi, Abstract Syntax and Variable Binding, LICS 1999: https://lics.siglog.org/1999/FiorePlotkinTuri-AbstractSyntaxandVa.html . Scope-indexed syntax with renaming/substitution and initial-algebra semantics.
2. Ahrens, Hirschowitz, Lafont, Maggesi, High-Level Signatures and Initial Semantics, CSL 2018: https://doi.org/10.4230/LIPIcs.CSL.2018.4 . Extensible signatures compatible with substitution.
3. Dybjer, Internal Type Theory, 1996: https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf . Contexts and substitutions, dependent families and comprehension.
4. Ranta, Grammatical Framework, JFP 2004: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/grammatical-framework/09C4B3F43447ADDB0F632C64F195BC9C . One abstract syntax, multiple concrete grammars.
5. Aarne Ranta, Symbolic Informalization, 2026 preprint: https://arxiv.org/abs/2606.16893 . Dedukti/GF interlingual architecture.

## Implemented scope model

lean/Scoped.lean defines Term n with Fin n variables and binders whose bodies are in Term (n+1). Renaming lifts under binders; simultaneous substitution shifts inserted terms to avoid capture. The model states renaming identity/composition and identity substitution. The concrete families model defines reindexing, its identity/composition and the projection/eta equations for dependent context extension. These are small scope and context laws, not an initiality theorem, complete CwF formalization, or full Lean calculus.

The browser formula parser also produces a canonical scoped view using de Bruijn indices; it retains original names in the surface AST for display and source output. Alpha-equivalent bound names produce identical scoped views, while free names remain unresolved until Lean. The built-in unary spellings `Not P` and `¬ P` share one scoped form; this is a syntax alias, not general definitional equality. The JS implementation is tested but has not been proved equivalent to the Lean model.

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

## Integration plan

Define a context-indexed typed signature with distinct object, proposition, proof and hole sorts. Connect native Expr export with explicit binding identity and universe data. Define a type-preserving elaboration relation from surface syntax, retaining alternative parses if not unique. A local edit becomes a partial context morphism and checked replacement, preserving the surrounding proof complement. Establish substitution composition and then a theorem connecting the actual serialized representation to its Lean interpretation. Only after this link should we claim end-to-end semantic correctness.

Regex is useful for lexical tokens and finite controlled phrase boundaries; a recursive parser is needed for nested formulas and binders. Plain LaTeX does not uniquely determine mathematical semantics; explicit typed annotations, context and user disambiguation are necessary. Lean LSP identifier completion and bounded proof search are complementary, not the same operation.

The controlled chain also admits explicit proof holes: `Establish h : $P$ | ?` and `Conclude | ?`. These lower to Lean `exact?` calls, not `sorry`. Every completed candidate is subject to the existing rebuilt-proof and structural checks, including rejection of references to the original theorem. Failure to solve a hole is an ordinary elaboration failure. No completeness or deterministic proof choice is claimed.

## Composition laws

Scoped.lean now also states mixed renaming/substitution equations and associativity of simultaneous substitution. Substitution arrows n → m are Fin n → Term m; their composition is substitution of the second arrow into the first. The direction is that of variable assignments (opposite to context maps Δ → Γ). Identity and associativity are stated for these arrows. This is the finite-context relative Kleisli construction for the scope syntax, not a claim of a typed category of all Lean terms or an initiality proof. CI checks these Lean proofs.

## Native judgment schema (version 1)

The on-demand #duet_ir command and /api/ir endpoint serialize the selected Lean judgment Γ ⊢ t : A. Context entries preserve declaration order, numeric local slots, structural names, binder mode, types and optional let values, including internal declarations. Terms use tagged arrays: bound (de Bruijn), local (slot), sort, const (structural name and universe instantiation), app, lambda, pi, let, nat, string, projection. Metadata is erased. Universe levels are structural; arbitrary-size literal naturals and numeric name components use decimal strings. An optional surface formula is elaborated as a proposition in the same local context and exported alongside its definitional equality result, not inferred from printed names. The browser validates constructor shape and lexical scope, not types. JSON is read-only, revision-local, and bounded; the encoder rejects unresolved metavariables and excessive depth/size. There is no external JSON import or source-provenance map yet. The native decoder is exercised internally in the original local context; see below. The source Lean environment remains necessary to interpret constants. This is the first bridge from the actual kernel representation, separate from the pedagogical occurrence tree and the surface AST.

### Formula-only proof sequences

The proof editor can switch to a formula-only surface syntax: one delimited LaTeX formula per line, optionally named for intermediate results. All earlier lines create typed proof holes; the last uses a `show` statement so that Lean must accept the proposition as the selected target. Generated intermediate names avoid supplied local names. The same structured steps and checked patch pipeline apply. No completeness or proof-choice guarantee is claimed.

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
