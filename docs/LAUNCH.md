# Community launch plan

Positioning: Two languages, one proof. A workbench for mathematical understanding, not a claim to automate theorem proving.

Before public announcement: pass real Lean CI, capture a 30–60 second actual demo, and document installation on Windows/macOS/Linux. Show a nested proof round trip, editing one line, source navigation, conflict rejection and Lean verification. Label AI explanation as unverified.

First audience: Lean Community Zulip (ask for technical feedback on InfoTree and proof alignment), mathematical reading groups (test narratives), Principia participants (invite examples), and related open-source maintainers (ask specific interoperability questions respectfully). Later: Hacker News and Reddit after the demo is usable. Do not mass-post or imply endorsement.

Contributors can help without programming by supplying a Lean proof, a handwritten explanation, and mappings or missing reasoning. Maintain public starter tasks with acceptance criteria. Respond constructively to critiques and give credit in release notes.

Draft announcement:
"I'm building LeanDuet, an open-source workbench exploring bidirectional editing between mathematical narratives and Lean 4. The current prototype preserves controlled proof syntax and links steps to source. The hard problem is semantic alignment: how do we preserve mathematical intent while changing a formal proof? I'm looking for collaborators and counterexamples, especially nested proofs, InfoTree extraction and readable mathematical explanations. https://github.com/Liangebra/leanduet"
