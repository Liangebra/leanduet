
-- Executed after the adapter is compiled in CI. No external JSON is executed.
namespace LeanDuetDecoderTests
open Lean LeanDuetExtract

def decodeFixture (input : String) : Except String Expr := do
  let j ← Json.parse input
  let (e, _) ← (decodeExpr #[] j).run 12000
  return e

def rejected (input : String) : Bool :=
  match decodeFixture input with
  | .error _ => true
  | .ok _ => false

#guard rejected "[\"bound\",0]"
#guard rejected "[\"local\",0]"
#guard rejected "[\"sort\",[\"unresolved\"]]"
#guard rejected "[\"sort\",[]]"
#guard rejected "[\"nat\",\"01\"]"
#guard rejected "[\"app\",[\"nat\",\"1\"]]"
#guard rejected "[\"const\",[[],\"num\",\"-1\"],[]]"
#guard rejected "[\"pi\",[[],\"str\",\"x\"],\"bad\",[\"sort\",[\"zero\"]],[\"bound\",0]]"
#guard match decodeFixture "[\"nat\",\"9007199254740993\"]" with
  | .ok (.lit (.natVal n)) => n == 9007199254740993
  | _ => false
#guard match decodeFixture "[\"lambda\",[[],\"str\",\"x\"],\"implicit\",[\"sort\",[\"zero\"]],[\"bound\",0]]" with
  | .ok (.lam (.str .anonymous "x") (.sort .zero) (.bvar 0) .implicit) => true
  | _ => false

end LeanDuetDecoderTests
