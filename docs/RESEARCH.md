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

### Structural fidelity after export

Definitional equality of proof terms is too weak (proof irrelevance). The exporter now checks reconstructed and re-elaborated expressions for structural equality after stripping metadata and alpha-renaming binders, retaining de Bruijn indices, applications, constants, types and binder information. If the pretty-printer and elaborator do not round-trip this shape, the preview is rejected. A structural no-op returns the original source byte-for-byte rather than reformatting the theorem. This is a deliberately conservative partial update, not an assertion that all Lean terms can round-trip. The local proof scope is included in the inspector. Tests distinguish two hypotheses of the same proposition, and exercise the typed replacement UI.

### Type-directed local alternatives

For proof-valued nodes the extractor compares each local declaration type to the node's inferred proposition using Lean's definitional equality. The editor offers unambiguous local names as guided replacement candidates. It still elaborates, checks, reconstructs and round-trips the chosen proof; this is local assumption selection, not a general proof search or a free-language parser.

## Dependent contexts and witness editing

lean/Dependent.lean models a context Γ as a type of environments, propositions as families Γ → Prop, and object types as families Γ → Type. Sigma extension represents a variable and Subtype extension represents an assumption. The indexed narrative supports universal introduction/elimination, existential introduction/elimination, implication and equality transport. The compiler is a shallow semantic interpretation; known leaves contain already supplied Lean evidence. It is not a complete syntax for Lean or a formal bridge to Expr.

A CertifiedWitness packages a section w and evidence in the fibre P(γ,w γ). Changing w requires evidence in the new fibre; equal carrier types alone are insufficient. transportSection illustrates how an equality of sections pointwise transports dependent data. In the native inspector, only the witness argument of Exists.intro is newly editable; the entire rebuilt term, type and shape are still checked. Changing a witness while retaining incompatible evidence must be rejected. For existential introduction, selecting the parent Exists.intro node now supports a paired witness/evidence edit. The frontend builds a candidate term, elaborated against the original existential proposition, so both dependent arguments change atomically. This is not yet a general multi-hole algorithm.

Bounded local application discovery tries one explicit Pi binder and up to 24 local declarations, returning at most eight matching applications at an application node. It substitutes the actual argument into the codomain and uses Lean definitional equality, including for ∀-elimination. No AI or arbitrary global theorem search is involved; all proposed terms require full patch validation. The previous reserved-keyword error in the extractor is corrected.

Deployment now checks that the tested SHA is the actual checkout, current main, and has a successful push CI run before publishing; manual deployment cannot bypass this gate.

## Type-indexed library search and controlled rule intent

The inspector now supports on-demand search at a particular Expr occurrence, using its actual local context. Lean 4.19's Lean.Meta.LibrarySearch.libSearchFindDecls is the imported-declaration discrimination-tree index; mkLibrarySearchLemma handles original declarations and both directions of iff. The adapter tries at most 48 candidates, solves subsidiary goals by bounded local elimination (depth 4), and returns at most six closed candidate terms. Each attempt restores its metavariable context. The selected theorem and its namespace auxiliaries are excluded from candidate use, and returned proof terms are checked for self-reference and sorryAx. Every exported edit must still pass the existing independent recompilation and proof-shape checks. This search is intentionally incomplete. It does not create new axioms or use an LLM.

The bilingual rule intent table is a reviewed finite lexicon, not free-language semantic understanding. Exact declaration names are accepted too. Mathlib entries are resolved against the actually loaded environment, not presumed available. The same search infrastructure can index Mathlib when used with a built compatible Lake project; CI currently tests core Lean only. See Lean upstream source at https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Meta/Tactic/LibrarySearch.lean (Apache-2.0); no upstream source is copied.

### Mathlib integration target

The optional Mathlib topology workflow uses the upstream v4.19.0 tag, which declares exactly the same Lean toolchain as this repository. It retrieves the cache for Mathlib.Topology.Compactness.Compact and executes tests/mathlib_integration.py against that independent Lake project. The test targets IsCompact.image (confirmed in the tagged upstream file), not a guessed translation or hand-coded theorem. The normal CI remains lightweight; the Mathlib job runs for changes to its test/workflow and is manually runnable. Success must be confirmed from its workflow log; availability of the cache and hosted runner is external.

### Explicit evidence constraints

The controlled phrase grammar accepts a mathematical rule followed by named local premises, for example "by transitivity of equality, using hab and hbc" or "由等式传递性，使用 hab、hbc". The frontend returns a structured rule identifier and list of names. Lean resolves these names to distinct local FVarIds, rejects missing or ambiguous names, passes still-unused premises into local elimination, and checks that the final expression contains every requested free-variable occurrence. This is a syntactic evidence-use contract, not a claim that the premises are mathematically indispensable. The search remains bounded and may miss a valid constrained proof.

### Sequential controlled proof language

A restricted compositional grammar compiles lines such as `Establish hq : Q | f using p` and `Conclude | g using hq` (also Chinese/Japanese line markers). Each intermediate declaration extends the visible scope; forward references, ambiguous references and name shadowing are rejected. The proposition annotation is Lean syntax and arguments are ordered, not merely a set of required occurrences. The compiler emits a candidate Lean term using have/exact. The existing local patch pipeline independently elaborates and checks the candidate and rejects structural export failures. The grammar does not infer arbitrary propositions, solve missing arguments or certify unrestricted natural language. The frontend parser's scope checks are usability constraints, not a security sandbox.

The semantic model additionally defines the cut-style `establish` operation as implication introduction followed by elimination; `establish_sound` states its evaluation equation, and `extendWithFact` is a section of context projection. This formalizes sequential context extension at the model level, not a mechanized correctness proof of the JavaScript parser. Application arguments are ordered and may repeat; explicit search-premise constraints remain distinct sets.
