# Selective language-design transfer

## Sources and decisions

- Sutherland, *Sketchpad* (1963), https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-574.html : retain object identity, local constraints and change propagation; do not require drawing proofs.
- Smith, *Pygmalion* (1975 thesis; 1977 book), https://link.springer.com/book/10.1007/978-3-0348-5744-4 : learn from examples of user operations; no mandatory icons.
- Teitelbaum and Reps, *The Cornell Program Synthesizer* (1981), https://research.cs.wisc.edu/wpis/abstracts/cacm81.abs.html : common structural representation; reject compulsory syntax-directed editing.
- Ranta, *Grammatical Framework* (2004), https://doi.org/10.1017/S0956796803004738 : distinguish abstract inference frames from language-specific forms.
- Tomita, *An Efficient Context-Free Parsing Algorithm for Natural Languages* (1985), https://ijcai.org/proceedings/1985/149 : retain alternatives; current bounded schema alternatives are not a general GLR parser or shared-packed forest.
- Wagner and Graham, *Efficient and Flexible Incremental Parsing* (1998), https://doi.org/10.1145/293677.293678 : retain stable structure across edits; apply to the draft compiler in future.
- Foster et al., *Combinators for Bidirectional Tree Transformations* (2007), https://www.cs.cornell.edu/~jnfoster/publications/ : retain source information when updating projections; not an assumption that free prose has a total inverse.
- Omar et al., *Hazelnut* (2017), https://doi.org/10.1145/3093333.3009900 : retain incomplete and inconsistent material; current untyped draft rows are not Hazelnut's typed editing calculus.
- *The Isabelle/Naproche Natural Language Proof Assistant* (2021), https://doi.org/10.1007/978-3-030-79876-5_36 : use mathematical discourse structure without replacing Lean or making controlled grammar mandatory.

## Implemented experiment: contextual inference frames

A premise-only phrase, for example "由 hbc 与 hab 得到 [goal]", preserves the exact named premises. A small structural matcher compares their parsed types with the target, generating candidate rule applications for direct reference, implication, equivalence, conjunction and elementary transitivity/symmetry. It considers both argument orders; repeated premises remain distinct references. Earlier translated intermediate statements can feed the following draft, but are not assumed to have been proved. Missing context, unsupported type syntax and competing interpretations remain unresolved. The chain compiler requires a unique structural candidate or an explicit rule. The existing interpretation panel can submit several candidates to Lean's independent local checks. This is a browser-only syntactic heuristic, not theorem proving, type inference, a full semantic parse forest, or assurance of intended meaning. The schema matcher compares parsed surface forms, not definitional equality; Lean remains the authority.

No third-party code or new runtime dependencies were imported. The next steps are typed discourse frames for declarations and quantifiers, explicit candidate choices for whole chains, dependency-indexed incremental parsing, and evaluation on aligned examples of human mathematical arguments.
