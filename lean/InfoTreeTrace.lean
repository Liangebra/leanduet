namespace LeanDuetExtract
open Lean Meta Elab Command

private structure TermReferences where
  termInfoCount : Nat := 0
  declarations : Array String := #[]
  locals : Array Json := #[]
  deriving Nonempty

private def mergeTermReferences (left right : TermReferences) : TermReferences := Id.run do
  let mut declarations := left.declarations
  for name in right.declarations do
    if !declarations.contains name then declarations := declarations.push name
  return {
    termInfoCount := left.termInfoCount + right.termInfoCount
    declarations := declarations
    locals := left.locals ++ right.locals
  }

private partial def expressionDeclarations : Expr → Array String
  | .const name _ => #[name.toString]
  | .proj name _ body => #[name.toString] ++ expressionDeclarations body
  | .app fn arg => expressionDeclarations fn ++ expressionDeclarations arg
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionDeclarations type ++ expressionDeclarations body
  | .letE _ type value body _ =>
      expressionDeclarations type ++ expressionDeclarations value ++ expressionDeclarations body
  | .mdata _ body => expressionDeclarations body
  | _ => #[]

private def referencesFromTerm (expr : Expr) (lctx : LocalContext) : TermReferences := Id.run do
  let mut locals := #[]
  let mut index := 0
  for declaration in lctx do
    if !declaration.isImplementationDetail && expr.containsFVar declaration.fvarId then
      locals := locals.push (Json.mkObj [
        ("name", toJson declaration.userName.toString),
        ("contextIndex", toJson index)
      ])
    index := index + 1
  return {
    termInfoCount := 1
    declarations := expressionDeclarations expr
    locals := locals
  }

private partial def collectTermReferences : InfoTree → TermReferences
  | .hole _ => {}
  | .context _ child => collectTermReferences child
  | .node (.ofTacticInfo _) _ => {}
  | .node (.ofTermInfo info) children =>
      children.foldl (fun acc child =>
        mergeTermReferences acc (collectTermReferences child))
        (referencesFromTerm info.expr info.lctx)
  | .node (.ofDelabTermInfo info) children =>
      children.foldl (fun acc child =>
        mergeTermReferences acc (collectTermReferences child))
        (referencesFromTerm info.expr info.lctx)
  | .node _ children =>
      children.foldl (fun acc child =>
        mergeTermReferences acc (collectTermReferences child)) {}

private def traceLocalContext : MetaM Json := do
  let mut entries := #[]
  let mut index := 0
  for declaration in (← getLCtx) do
    if !declaration.isImplementationDetail then
      entries := entries.push (Json.mkObj [
        ("name", toJson declaration.userName.toString),
        ("contextIndex", toJson index),
        ("type", toJson (← ppExpr declaration.type).pretty)
      ])
    index := index + 1
  return Json.arr entries

private def traceGoalJson (ctx : ContextInfo) (mctx : MetavarContext)
    (goal : MVarId) : IO Json := do
  ({ctx with mctx := mctx}).runMetaM {} do
    goal.withContext do
      let target ← goal.getType
      return Json.mkObj [
        ("target", toJson (← ppExpr target).pretty),
        ("localContext", ← traceLocalContext)
      ]

private def traceGoalsJson (ctx : ContextInfo) (mctx : MetavarContext)
    (goals : List MVarId) : IO Json := do
  let mut entries := #[]
  for goal in goals do
    entries := entries.push (← traceGoalJson ctx mctx goal)
  return Json.arr entries

private def tracePositionJson (position : Position) : Json :=
  Json.mkObj [
    ("line", toJson position.line),
    ("column", toJson position.column)
  ]

private def traceRangeJson (fileMap : FileMap) (stx : Syntax) : Json :=
  match stx.getRange? true with
  | none => Json.null
  | some range =>
    let start := fileMap.toPosition range.start
    let stop := fileMap.toPosition range.stop
    Json.mkObj [
      ("startByte", toJson range.start.byteIdx),
      ("endByte", toJson range.stop.byteIdx),
      ("start", tracePositionJson start),
      ("end", tracePositionJson stop)
    ]

private partial def countTacticNodes : InfoTree → Nat
  | .hole _ => 0
  | .context _ child => countTacticNodes child
  | .node (.ofTacticInfo _) children =>
      1 + children.foldl (fun count child => count + countTacticNodes child) 0
  | .node _ children =>
      children.foldl (fun count child => count + countTacticNodes child) 0

private def referencesFromAssignedGoals (ctx? : Option ContextInfo) (info : TacticInfo)
    : IO (TermReferences × Nat × Bool) := do
  let some ctx := ctx? | return ({}, 0, false)
  let mut references : TermReferences := {}
  let mut assignmentCount := 0
  let mut allAssignmentsClosed := true
  for goal in info.goalsBefore do
    if let some rawAssignment := info.mctxAfter.getExprAssignmentCore? goal then
      assignmentCount := assignmentCount + 1
      let localContext ← ({ctx with mctx := info.mctxBefore}).runMetaM {} do
        goal.withContext do getLCtx
      let assignment ← ({ctx with mctx := info.mctxAfter}).runMetaM {} do
        instantiateMVars rawAssignment
      if assignment.hasExprMVar then
        allAssignmentsClosed := false
      let termReferences := referencesFromTerm assignment localContext
      references := mergeTermReferences references {termReferences with termInfoCount := 0}
  return (references, assignmentCount, assignmentCount > 0 && allAssignmentsClosed)

private def traceTacticJson (fileMap : FileMap) (ctx? : Option ContextInfo)
    (info : TacticInfo) (children : PersistentArray InfoTree) : IO Json := do
  let termReferences := children.foldl (fun acc child =>
    mergeTermReferences acc (collectTermReferences child)) {}
  let (assignedReferences, assignmentCount, assignmentsClosed) ←
    referencesFromAssignedGoals ctx? info
  let references := mergeTermReferences termReferences assignedReferences
  let range := traceRangeJson fileMap info.stx
  let (before, after) ← match ctx? with
    | none => pure (Json.arr #[], Json.arr #[])
    | some ctx => do
      pure (← traceGoalsJson ctx info.mctxBefore info.goalsBefore,
            ← traceGoalsJson ctx info.mctxAfter info.goalsAfter)
  let isOpaque := references.termInfoCount == 0
  return Json.mkObj [
    ("syntax", toJson (info.stx.reprint.getD (toString info.stx))),
    ("sourceRange", range),
    ("contextAvailable", toJson ctx?.isSome),
    ("goalsBefore", before),
    ("goalsAfter", after),
    ("termInfoCount", toJson references.termInfoCount),
    ("assignedProofTermCount", toJson assignmentCount),
    ("assignedProofTermsClosed", toJson assignmentsClosed),
    ("referencedDeclarations", toJson references.declarations),
    ("referencedLocals", Json.arr references.locals),
    ("opaque", toJson isOpaque),
    ("opaqueRange", if isOpaque then range else Json.null),
    ("opaqueMapping", if isOpaque then
      toJson "No child TermInfo expression was recorded; opaque tactic syntax maps to sourceRange. References may still be observed from assigned goals."
      else Json.null)
  ]

private partial def collectTacticTrace (fileMap : FileMap) (tree : InfoTree)
    (ctx? : Option ContextInfo := none) : IO (Array Json) := do
  match tree with
  | .hole _ => return #[]
  | .context partialCtx child =>
      collectTacticTrace fileMap child (partialCtx.mergeIntoOuter? ctx?)
  | .node info children =>
      let mut entries := #[]
      if let .ofTacticInfo tacticInfo := info then
        entries := entries.push (← traceTacticJson fileMap ctx? tacticInfo children)
      let childContext := Info.updateContext? ctx? info
      for child in children do
        entries := entries ++ (← collectTacticTrace fileMap child childContext)
      return entries

elab "#duet_trace " declaration:command : command => do
  let fileMap ← getFileMap
  let (tactics, infoTreeEnabled, infoTreeCount, tacticInfoCount) ←
    withEnableInfoTree true do
      elabCommandTopLevel declaration
      let infoState ← getInfoState
      -- InfoTree holes may be fulfilled by synchronous assignments or deferred tasks.
      -- Resolve both before inspecting tactic nodes, as Lean does for snapshots.
      let resolvedInfoState := infoState.substituteLazy.get
      let trees := resolvedInfoState.trees.map
        (fun tree => tree.substitute resolvedInfoState.assignment)
      let mut tactics := #[]
      for tree in trees do
        tactics := tactics ++ (← collectTacticTrace fileMap tree)
      let tacticCount := trees.foldl
        (fun count tree => count + countTacticNodes tree) 0
      pure (tactics, infoState.enabled, trees.size, tacticCount)
  let result := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("infoTreeEnabled", toJson infoTreeEnabled),
    ("infoTreeCount", toJson infoTreeCount),
    ("tacticInfoCount", toJson tacticInfoCount),
    ("tactics", Json.arr tactics)
  ]
  logInfo m!"LEANDUET_TRACE_JSON:{result.compress}"

end LeanDuetExtract
