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

The browser formula parser also produces a canonical scoped view using de Bruijn indices; it retains original names in the surface AST for display and source output. Alpha-equivalent bound names produce identical scoped views, while free names remain unresolved until Lean. The JS implementation is tested but has not been proved equivalent to the Lean model.

## Integration plan

Define a context-indexed typed signature with distinct object, proposition, proof and hole sorts. Connect native Expr export with explicit binding identity and universe data. Define a type-preserving elaboration relation from surface syntax, retaining alternative parses if not unique. A local edit becomes a partial context morphism and checked replacement, preserving the surrounding proof complement. Establish substitution composition and then a theorem connecting the actual serialized representation to its Lean interpretation. Only after this link should we claim end-to-end semantic correctness.

Regex is useful for lexical tokens and finite controlled phrase boundaries; a recursive parser is needed for nested formulas and binders. Plain LaTeX does not uniquely determine mathematical semantics; explicit typed annotations, context and user disambiguation are necessary. Lean LSP identifier completion and bounded proof search are complementary, not the same operation.

The controlled chain also admits explicit proof holes: `Establish h : $P$ | ?` and `Conclude | ?`. These lower to Lean `exact?` calls, not `sorry`. Every completed candidate is subject to the existing rebuilt-proof and structural checks, including rejection of references to the original theorem. Failure to solve a hole is an ordinary elaboration failure. No completeness or deterministic proof choice is claimed.

## Composition laws

Scoped.lean now also states mixed renaming/substitution equations and associativity of simultaneous substitution. Substitution arrows n → m are Fin n → Term m; their composition is substitution of the second arrow into the first. The direction is that of variable assignments (opposite to context maps Δ → Γ). Identity and associativity are stated for these arrows. This is the finite-context relative Kleisli construction for the scope syntax, not a claim of a typed category of all Lean terms or an initiality proof. CI checks these Lean proofs.

## Native judgment schema (version 1)

The on-demand #duet_ir command and /api/ir endpoint serialize the selected Lean judgment Γ ⊢ t : A. Context entries preserve declaration order, numeric local slots, structural names, binder mode, types and optional let values, including internal declarations. Terms use tagged arrays: bound (de Bruijn), local (slot), sort, const (structural name and universe instantiation), app, lambda, pi, let, nat, string, projection. Metadata is erased. Universe levels are structural; arbitrary-size literal naturals and numeric name components use decimal strings. An optional surface formula is elaborated as a proposition in the same local context and exported alongside its definitional equality result, not inferred from printed names. The browser validates constructor shape and lexical scope, not types. JSON is read-only, revision-local, and bounded; the encoder rejects unresolved metavariables and excessive depth/size. There is no import or decoder yet, no claimed source provenance or full roundtrip theorem. The source Lean environment remains necessary to interpret constants. This is the first bridge from the actual kernel representation, separate from the pedagogical occurrence tree and the surface AST.

### Formula-only proof sequences

The proof editor can switch to a formula-only surface syntax: one delimited LaTeX formula per line, optionally named for intermediate results. All earlier lines create typed proof holes; the last uses a `show` statement so that Lean must accept the proposition as the selected target. Generated intermediate names avoid supplied local names. The same structured steps and checked patch pipeline apply. No completeness or proof-choice guarantee is claimed.
