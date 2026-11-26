# Proof IR v2: lexical, not semantic

The current IR is deliberately small and shared by all future clients. Each document contains version, prelude, header, nodes and finalNewline. Each nonblank node contains a source line, indentation, Lean fragment, controlled-language label, argument, and parent ID. A parent is the nearest preceding less-indented proof line, not a logical dependency. IDs are revision-local line IDs, not persistent identities.

## Laws to test

For supported LF sources S, renderLean(parseLean(S)) = S. For a parsed IR I, renderLean(parseProse(renderProse(I))) = renderLean(I). Sync must refuse concurrent edits and changes to the declaration header or import environment. Neither law implies mathematical equivalence of free prose.

## Next semantic layer

Keep the source-preserving lexical adapter separate from an elaboration adapter that exports goal-before/after, local context, referenced declarations, ranges, and diagnostics from Lean InfoTree. Align narrative nodes many-to-many to tactic ranges. Preserve opaque subproofs until their mathematical content is established. Add revision-aware stable IDs, incremental patches, and an independent alignment status (unreviewed / human-reviewed / formally specified). Lean validity and narrative alignment must never share one green check.

Clients should use the same core and checker protocol. Desktop and VS Code adapters can replace transport and rendering without reimplementing the conversion rules.
