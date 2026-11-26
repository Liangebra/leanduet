-- Appended after a trusted source file (import Lean is added by the driver).
-- The output is an explanatory tree, NOT a lossless Expr serialization.
namespace LeanDuetExtract
open Lean Meta Elab Command

def node (kind term type : String) (children : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("kind", toJson kind), ("term", toJson term), ("type", toJson type),
    ("children", Json.arr children)] ++ extra)

partial def inspect (e : Expr) (fuel : Nat) : MetaM Json := do
  let term := (← ppExpr e).pretty
  let ty ← inferType e
  let typ := (← ppExpr ty).pretty
  if fuel == 0 then return node "opaque" term typ
  match e with
  | .lam n t b bi =>
      let binderType := (← ppExpr t).pretty
      let kind := if ← isProp t then "assume" else "introduce"
      withLocalDecl n bi t fun x => do
        let child ← inspect (b.instantiate1 x) (fuel - 1)
        return node kind term typ #[child]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .letE n t v b _ =>
      let binderType := (← ppExpr t).pretty
      let value ← inspect v (fuel - 1)
      withLetDecl n t v fun x => do
        let body ← inspect (b.instantiate1 x) (fuel - 1)
        return node "let" term typ #[value, body]
          [("binder", toJson n.toString), ("binderType", toJson binderType)]
  | .app .. =>
      let head := e.getAppFn
      let headText := (← ppExpr head).pretty
      let headType := (← ppExpr (← inferType head)).pretty
      let mut children := #[]
      for a in e.getAppArgs do
        if ← isProp (← inferType a) then
          if children.size < 8 then
            children := children.push (← inspect a (fuel - 1))
      let ref := match head with
        | .const n _ => n.toString
        | _ => headText
      return node "apply" term typ children
        [("reference", toJson ref), ("referenceType", toJson headType)]
  | .const n _ => return node "reference" term typ #[] [("reference", toJson n.toString)]
  | .fvar _ => return node "hypothesis" term typ
  | .mdata _ body => inspect body (fuel - 1)
  | _ => return node "opaque" term typ

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

end LeanDuetExtract
