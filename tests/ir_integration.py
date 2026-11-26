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
