-- Appended after a trusted source file (import Lean is added by the driver).
-- The output is an explanatory tree, NOT a lossless Expr serialization.
namespace LeanDuetExtract
open Lean Meta Elab Command

def node (path : String) (editable : Bool) (scope : Array Json) (kind term type : String) (children : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("kind", toJson kind), ("term", toJson term), ("type", toJson type),
    ("children", Json.arr children), ("path", toJson path), ("editable", toJson editable), ("scope", Json.arr scope)] ++ extra)

-- Preserve variable occurrences and proof constructors: not definitional equality.
-- Alpha-renaming and source metadata are intentionally ignored.
partial def shape (e : Expr) : Expr :=
  match e with
  | .mdata _ b => shape b
  | .lam _ t b bi => .lam .anonymous (shape t) (shape b) bi
  | .forallE _ t b bi => .forallE .anonymous (shape t) (shape b) bi
  | .letE _ t v b _ => .letE .anonymous (shape t) (shape v) (shape b) false
  | .app f a => .app (shape f) (shape a)
  | .proj n i b => .proj n i (shape b)
  | _ => e

def sameShape (a b : Expr) : Bool := Expr.equal (shape a) (shape b)

def localScope (goal : Expr) (editable : Bool) : MetaM (Array Json) := do
  let mut entries := #[]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then
      let matchesType ← if editable then isDefEq d.type goal else pure false
      entries := entries.push (Json.mkObj [
        ("matchesGoal", toJson matchesType), ("name", toJson d.userName.toString),
        ("type", toJson (← ppExpr d.type).pretty)])
  return entries

-- Bounded local application search. Instantiate a single explicit dependent
-- binder with a local object, then compare the resulting proposition in Lean.
def localApplications (goal : Expr) : MetaM (Array Json) := do
  let mut locals : Array LocalDecl := #[]
  for d in (← getLCtx) do
    if !d.isImplementationDetail && locals.size < 24 then
      locals := locals.push d
  let mut results := #[]
  for f in locals do
    let ty ← whnf f.type
    match ty with
    | .forallE _ domain body .default =>
      for a in locals do
        if results.size < 8 then
          if ← isDefEq a.type domain then
            let resultType := body.instantiate1 (mkFVar a.fvarId)
            if ← isDefEq resultType goal then
              results := results.push (Json.mkObj [
                ("function", toJson f.userName.toString),
                ("argument", toJson a.userName.toString),
                ("type", toJson (← ppExpr resultType).pretty)])
    | _ => pure ()
  return results

def isWitnessArg (head : Expr) (i : Nat) : Bool :=
  match head with
  | .const n _ => n == `Exists.intro && i == 2
  | _ => false

partial def inspect (e : Expr) (fuel : Nat) (path : String := "root") : MetaM Json := do
  let term := (← ppExpr e).pretty
  let ty ← inferType e
  let typ := (← ppExpr ty).pretty
  let editable ← isProp ty
  let scope ← localScope ty editable
  if fuel == 0 then return node path editable scope "opaque" term typ
  match e with
  | .lam n t b bi =>
      let binderType := (← ppExpr t).pretty
      let kind := if ← isProp t then "assume" else "introduce"
      withLocalDecl n bi t fun x => do
        let child ← inspect (b.instantiate1 x) (fuel - 1) (path ++ "/body")
        return node path editable scope kind term typ #[child]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .letE n t v b _ =>
      let binderType := (← ppExpr t).pretty
      let value ← inspect v (fuel - 1) (path ++ "/value")
      withLetDecl n t v fun x => do
        let body ← inspect (b.instantiate1 x) (fuel - 1) (path ++ "/body")
        return node path editable scope "let" term typ #[value, body]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .app .. =>
      let alternatives ← if editable then localApplications ty else pure #[]
      let head := e.getAppFn
      let headText := (← ppExpr head).pretty
      let headType := (← ppExpr (← inferType head)).pretty
      let mut children := #[]
      let args := e.getAppArgs
      for i in [:args.size] do
        let a := args[i]!
        let argPath := path ++ "/arg" ++ toString i
        if isWitnessArg head i then
          let aType ← inferType a
          let aScope ← localScope aType true
          children := children.push (node argPath true aScope "witness"
            (← ppExpr a).pretty (← ppExpr aType).pretty)
        else if ← isProp (← inferType a) then
          if children.size < 8 then
            children := children.push (← inspect a (fuel - 1) argPath)
      let ref := match head with
        | .const n _ => n.toString
        | _ => headText
      return node path editable scope "apply" term typ children
        [("reference", toJson ref), ("referenceType", toJson headType), ("applications", Json.arr alternatives)]
  | .const n _ => return node path editable scope "reference" term typ #[] [("reference", toJson n.toString)]
  | .fvar _ => return node path editable scope "hypothesis" term typ
  | .mdata _ body => inspect body (fuel - 1) path
  | _ => return node path editable scope "opaque" term typ

elab "#duet_extract " n:ident : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      let result ← inspect v.value 10
      let j := Json.mkObj [("schema", toJson (1 : Nat)), ("declaration", toJson n.getId.toString),
        ("tree", result)]
      logInfo m!"LEANDUET_JSON:{j.compress}"
    | _ => throwError "Expected a theorem"

/-- Rebuild exactly one expression path, elaborating the replacement in its actual scope. -/
partial def replaceAt (e : Expr) (path : List String) (stx : Syntax)
    (allowWitness : Bool := false) : TermElabM (Expr × String × String) := do
  match path with
  | [] =>
    let ty ← inferType e
    unless allowWitness || (← isProp ty) do throwError "Only proofs and existential witness positions are editable"
    let value ← Term.elabTermEnsuringType stx (some ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then throwError "Unresolved metavariables in replacement"
    Lean.Meta.check value
    unless ← isDefEq (← inferType value) ty do throwError "Replacement has the wrong local type"
    return (value, (← ppExpr ty).pretty, (← ppExpr e).pretty)
  | p :: rest =>
    match e with
    | .mdata md body =>
      let (v, ty, old) ← replaceAt body path stx
      return (.mdata md v, ty, old)
    | .lam n t b bi =>
      unless p == "body" do throwError "Invalid lambda path"
      withLocalDecl n bi t fun x => do
        let (v, ty, old) ← replaceAt (b.instantiate1 x) rest stx
        return (.lam n t (v.abstract #[x]) bi, ty, old)
    | .letE n t v b nd =>
      if p == "value" then
        let (v', ty, old) ← replaceAt v rest stx
        return (.letE n t v' b nd, ty, old)
      else if p == "body" then
        withLetDecl n t v fun x => do
          let (b', ty, old) ← replaceAt (b.instantiate1 x) rest stx
          return (.letE n t v (b'.abstract #[x]) nd, ty, old)
      else throwError "Invalid let path"
    | .app .. =>
      unless p.startsWith "arg" do throwError "Invalid application path"
      let some i := (String.mk (p.toList.drop 3)).toNat? | throwError "Invalid argument index"
      let args := e.getAppArgs
      unless i < args.size do throwError "Argument index out of bounds"
      let (v, ty, old) ← replaceAt args[i]! rest stx (isWitnessArg e.getAppFn i && rest.isEmpty)
      return (mkAppN e.getAppFn (args.set! i v), ty, old)
    | _ => throwError "Invalid expression path"

elab "#duet_patch " n:ident path:str replacement:str : command => do
  liftTermElabM do
    let ci ← getConstInfo n.getId
    match ci with
    | .thmInfo v =>
      unless v.levelParams.isEmpty do
        throwError "Universe-polymorphic theorem export is not yet supported"
      let parts := path.getString.splitOn "/"
      unless parts.head? == some "root" do throwError "Invalid root path"
      let stx ← match Parser.runParserCategory (← getEnv) `term replacement.getString with
        | .ok stx => pure stx
        | .error err => throwError "{err}"
      let (newProof, localType, oldTerm) ← replaceAt v.value (parts.drop 1) stx
      if newProof.hasMVar || newProof.hasLevelMVar || newProof.hasFVar || newProof.hasLooseBVars then
        throwError "Rebuilt proof is not closed"
      Lean.Meta.check newProof
      unless ← isDefEq (← inferType newProof) v.type do
        throwError "The entire proof no longer has the original type"
      let (typeText, termText) ← withOptions (fun o => o.setBool `pp.fullNames true) do
        pure ((← ppExpr v.type).pretty, (← ppExpr newProof).pretty)
      let j := Json.mkObj [("schema", toJson (1 : Nat)), ("type", toJson typeText),
        ("term", toJson termText), ("localType", toJson localType), ("oldTerm", toJson oldTerm),
        ("unchanged", toJson (sameShape newProof v.value))]
      logInfo m!"LEANDUET_JSON:{j.compress}"
    | _ => throwError "Expected a theorem"

elab "#duet_compare " n:ident m:ident path:str replacement:str : command => do
  liftTermElabM do
    let a ← getConstInfo n.getId
    let b ← getConstInfo m.getId
    unless ← isDefEq a.type b.type do throwError "Candidate declaration type changed"
    match a, b with
    | .thmInfo x, .thmInfo y =>
      let stx ← match Parser.runParserCategory (← getEnv) `term replacement.getString with
        | .ok stx => pure stx
        | .error err => throwError "{err}"
      let (expected, _, _) ← replaceAt x.value ((path.getString.splitOn "/").drop 1) stx
      unless sameShape expected y.value do
        throwError "Re-elaborated export does not preserve the requested proof structure"
      logInfo "LEANDUET_TYPE_AND_SHAPE_MATCH"
    | _, _ => throwError "Expected two theorems"

end LeanDuetExtract
