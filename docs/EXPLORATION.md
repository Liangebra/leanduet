# Mathematical exploration and formal commitment

Mathematics does not begin with a fully specified calculus. A mathematician may introduce a provisional notation, try an analogy, draw a conjecture, or change the question. LeanDuet should support this activity without forcing every sentence to become a formal command.

The Explore view stores arbitrary text independently of the controlled proof and Lean source. It has no grammar, no compulsory check, no AI requirement. It is exported verbatim as Markdown or included in a workspace export. Editing notes must not invalidate a Lean verification result for unchanged source.

A selected typed goal can be copied to exploration as a historical context snapshot. It is not a live assertion of correctness. The snapshot and subsequent ideas stay unverified. A selected delimited formula can be staged in goal search when a current proof goal is selected; only that selection is parsed. Parsing is not proof, and searching is not applying a proof. Neither action rewrites the surrounding notes or Lean source. Unsupported notation is kept verbatim in exploration.

The optional AI assistance is a separate, user-initiated operation. AI explanations append to notes with an unverified label rather than replacing the author's reasoning. A Lean proposal remains unverified until independently checked.

Our typed intermediate language describes the committed formal part of a document, not the limits of mathematical thought. Future work may include free-standing notebooks, multiple simultaneous conjectures, diagrams and local definitions, but none is implied by the current implementation.

## Working-object interface

The optional collection in the existing workspace format records stable local IDs, arbitrary labels, raw expressions, comments, informal references and author-assigned research statuses. Duplicate labels, empty expressions, cycles, dangling references, contradictory or unparseable statements are allowed. `discarded` retains the original attempt; `Try an alternative` creates a new object rather than overwriting it. These records are neither Lean declarations nor hypotheses. They have no inferred types and no automatic dependency resolution. The only mandatory validation is transport shape and storage limits (100 objects, bounded fields). Old workspaces without the optional collection restore to an empty collection. Markdown exports label every object unverified. A future semantic interface may attach a separately checked judgment to an object, without changing its raw expression.

A working object can be staged directly as a goal candidate. This is optional and uses only the selected expression, with the current typed goal as context; failed staging reports a diagnostic but leaves the original working object unchanged. Informal references are not interpreted as Lean assumptions. The local storage status is shown separately from mathematical status.
