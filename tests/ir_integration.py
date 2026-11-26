"""Actual structural Lean judgment and formula elaboration, independent of pretty printing."""
from pathlib import Path
import json, subprocess, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract,inspect_ir

def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)

def validate(ir):
    assert ir["judgment"]["roundTrip"]=={"checked":True,"shapePreserved":True,"encodingPreserved":True,"typeDefEq":True,"freshContextChecked":True,"mode":"same-environment-fresh-context"},ir
    script="import {validateJudgment} from './web/semantic-ir.mjs'; import fs from 'node:fs'; validateJudgment(JSON.parse(fs.readFileSync(0,'utf8')));"
    subprocess.run(["node","--input-type=module","-e",script],input=json.dumps(ir),text=True,check=True,cwd=Path(__file__).resolve().parents[1])

source="""theorem ir_identity (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
node=next(n for n in walk(extract(source)["tree"]) if n.get("term")=="h1" and n["kind"]=="hypothesis")
ir=inspect_ir(source,node["path"],"P")
validate(ir)
j=ir["judgment"]
ctx={d["display"]:d for d in j["context"]}
assert j["term"]==["local",ctx["h1"]["slot"]],ir
assert j["type"]==["local",ctx["P"]["slot"]],ir
assert j["formula"]["term"]==j["type"] and j["formula"]["matchesGoal"],ir
assert ctx["h1"]["slot"]!=ctx["h2"]["slot"],ir
assert inspect_ir(source,node["path"],"True")["judgment"]["formula"]["matchesGoal"] is False
root=inspect_ir(source,"root")
validate(root)
assert root["judgment"]["term"][0]=="lambda"
print("Kernel judgment retains local identity, bound variables and typed formula alignment")

source2="""theorem ir_universe (A : Type u) (x : A) : x = x := by
  rfl
"""
root=inspect_ir(source2,"root")
validate(root)
assert root["universes"],root
assert root["judgment"]["term"][0]=="lambda",root
print("Universe-polymorphic read-only IR preserves level parameters")

# Dependent binder, local let, constant universes, literals and applications.
source3="""theorem ir_dependent (n : Nat) (x : Fin (n+1)) : ∃ y : Fin (n+1), y = x := by
  let y := x
  exact ⟨y, rfl⟩
"""
validate(inspect_ir(source3,"root"))
tree=extract(source3)["tree"]
for node in walk(tree):
    if node["kind"]=="witness":
        validate(inspect_ir(source3,node["path"]))
        break
else:
    raise AssertionError("Expected existential witness")
print("Dependent expressions and selected witness survive structural decoding")


from semantic import abstract_preview
source4="""theorem ir_abstract (n : Nat) (f : Fin (n+1) → True) (x : Fin (n+1)) (irrelevant : Nat) : True := by
  exact f x
"""
target=next(n for n in walk(extract(source4)["tree"]) if n.get("reference")=="f")
a=abstract_preview(source4,target["path"])
assert a["closedChecked"] and a["reopenedShape"],a
assert [p["name"] for p in a["parameters"]]==["n","f","x"],a
assert a["standaloneChecked"] and a["exportShapePreserved"] and a["source"],a
assert "theorem LeanDuetExtractedLemma" in a["source"] and "irrelevant" not in a["source"],a
print("Dependency-closed abstraction compiles independently and preserves the proof occurrence")


# Same-type premises remain distinct during abstraction, not just serialization.
a=abstract_preview(source,next(n["path"] for n in walk(extract(source)["tree"]) if n.get("term")=="h1" and n["kind"]=="hypothesis"))
assert [p["name"] for p in a["parameters"]]==["P","h1"],a
assert a["standaloneChecked"] and a["exportShapePreserved"],a
# Universe-polymorphic abstraction is internally checked but not presented as standalone source.
u=abstract_preview(source2,"root")
assert u["closedChecked"] and u["reopenedShape"] and u["universes"],u
assert u["source"] is None and not u["standaloneChecked"],u
print("Abstraction preserves distinct premises and reports the polymorphic export limit")
