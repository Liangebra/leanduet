# Lean tactic trace: JSON schema 1

## Purpose and limits

The local `POST /api/trace` endpoint asks Lean to elaborate one declaration
and returns its resolved InfoTree observations. Capture is explicit and
on-demand; it does not run on every keystroke and does not call an AI service.
The endpoint is available only through the local server. The current request
limit is 12 KiB of UTF-8 source.

The adapter targets the repository's pinned Lean 4.19 toolchain. It accepts
imports before one declaration; arbitrary preceding declarations, namespaces,
or local notation are outside this first adapter. A Mathlib project can be
selected when starting the local server. Lean must elaborate the supplied
declaration before the trace is returned.

The trace reports what Lean recorded. It does not infer mathematical
dependencies from indentation, identify the author's intended proof route,
align a tactic with a prose sentence, or certify that the natural-language
reading is faithful. A tactic can produce more than one InfoTree node, and a
parent tactic such as `constructor` can cover an entire nested block.

## Top-level object

| Field | Type | Meaning |
| --- | --- | --- |
| `schema` | integer | Schema version; currently `1`. |
| `declaration` | string | Name of the traced Lean declaration. |
| `infoTreeEnabled` | boolean | Whether Lean InfoTree collection was enabled. |
| `infoTreeCount` | integer | Number of resolved top-level InfoTrees. |
| `tacticInfoCount` | integer | Raw number of TacticInfo nodes found in those trees before coalescing. |\n| `tacticObservationCount` | integer | Number of source/goal observations exposed in `tactics` after exact duplicate wrappers are coalesced. |
| `tactics` | array | Tactic records in depth-first InfoTree traversal order. |
| `sourceEncoding` | string | Currently `UTF-8`. |
| `rangeConvention` | string | Range and position convention, repeated in the response for clients. |

The adapter resolves synchronous and deferred InfoTree assignments before
traversal. Repeated wrappers are coalesced only when source range, reprinted
syntax, context availability, and goals before/after all match. The first
occurrence sets display order; `infoNodeCount` preserves raw multiplicity.
Unranged nodes are not coalesced. Neither raw nodes nor coalesced observations
are source-line counts.

## Tactic record

| Field | Type | Meaning |
| --- | --- | --- |
| `syntax` | string | Lean's reprinted syntax for the tactic node. It may include surrounding whitespace. |\n| `infoNodeCount` | integer | Number of raw TacticInfo wrappers coalesced into this identical source/syntax/context/goal observation. |
| `sourceRange` | range or null | Mapped half-open range in the original submitted source. |
| `contextAvailable` | boolean | Whether a Lean context was attached to the node. |
| `goalsBefore`, `goalsAfter` | arrays | Lean metavariable goals before and after this node. |
| `termInfoCount` | integer | Maximum child TermInfo/DelabTermInfo expression count among wrappers coalesced into this observation. |
| `assignedProofTermCount` | integer | Maximum count across wrappers of goals from `goalsBefore` assigned in the node's post-state. |
| `assignedProofTermsClosed` | boolean | True only when at least one such assignment exists and each assigned expression has no remaining expression metavariables after instantiation. This is not a statement about authorial intent. |
| `referencedDeclarations` | string array | Deduplicated constants occurring syntactically in recorded term expressions or assigned proof terms. |
| `referencedLocals` | object array | Deduplicated local variables occurring syntactically in those expressions; each has a display `name` and a context-local `contextIndex`. |
| `opaque` | boolean | True exactly when the coalesced `termInfoCount` is zero. It means no child TermInfo was recorded for any coalesced wrapper, not that the tactic has no proof term. |
| `opaqueRange` | range or null | When opaque, the whole `sourceRange`; otherwise null. |
| `opaqueMapping` | string or null | Explains the opaque-range mapping and that assigned-goal references may still be present. |

A goal record contains `target` (Lean pretty-printed text) and
`localContext` (an array of `name`, `contextIndex`, and pretty-printed
`type`). Context indices are positions within that observation, not persistent
object identities across edits. Reference arrays may reflect what occurs
syntactically in elaborated terms; they are not a transitive declaration
closure, a proof-minimization result, or a claim that every occurrence is
logically necessary.

A range object is `null` when Lean provides no source range. Otherwise it has
`startByte`, `endByte`, `start`, and `end`. Offsets are half-open UTF-8
byte offsets into the original request. Positions have 1-based lines and
0-based Unicode-scalar columns. Byte offsets and columns therefore differ
around non-ASCII text.

## Deterministic example

This excerpt is the `exact hp` record from the pinned integration fixture.
The fixture includes an imported `Lean` prelude and a non-ASCII comment before
the tactic, so the byte range verifies the adapter-preamble remapping.

```json
{
  "syntax": "exact hp\\n  ",
  "sourceRange": {
    "startByte": 159,
    "endByte": 167,
    "start": { "line": 6, "column": 4 },
    "end": { "line": 6, "column": 12 }
  },
  "contextAvailable": true,
  "goalsBefore": [
    {
      "target": "P",
      "localContext": [
        { "name": "P", "contextIndex": 1, "type": "Prop" },
        { "name": "Q", "contextIndex": 2, "type": "Prop" },
        { "name": "hp", "contextIndex": 3, "type": "P" },
        { "name": "hq", "contextIndex": 4, "type": "Q" }
      ]
    }
  ],
  "goalsAfter": [],
  "infoNodeCount": 3,
  "termInfoCount": 2,
  "assignedProofTermCount": 1,
  "assignedProofTermsClosed": true,
  "referencedDeclarations": [],
  "referencedLocals": [{ "name": "hp", "contextIndex": 3 }],
  "opaque": false,
  "opaqueRange": null,
  "opaqueMapping": null
}
```

The integration test checks the schema, deterministic repeat output, duplicate
wrapper coalescing, this local reference and assignment behavior, the
source-byte slice, nested conjunction goals, and the opaque `assumption`
mapping. The browser smoke test
captures a trace only after an explicit user action and verifies the localized
goal display. These checks validate the adapter behavior, not a prose/Lean
round trip.
