"""Actual Lean extraction smoke test; requires the pinned Lean toolchain."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract
source = """theorem composition (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  exact hqr (hpq hp)
"""
r=extract(source)
assert r["schema"]==1 and r["declaration"]=="composition",r
def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)
nodes=list(walk(r["tree"]))
assert any(n["kind"]=="assume" for n in nodes),nodes
assert any(n["kind"]=="apply" and "hqr" in n.get("reference","") for n in nodes),nodes
assert any(n["kind"]=="apply" and "hpq" in n.get("reference","") for n in nodes),nodes
print("Actual elaborated proof term extracted:",len(nodes),"nodes")


from semantic import patch
source2 = """theorem patch_example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hq : Q) : P → R := by
  intro hp
  exact hqr (hpq hp)
"""
tree=extract(source2)["tree"]
target=next(n for n in walk(tree) if n["kind"]=="apply" and n.get("reference")=="hpq")
assert target["editable"] and target["path"].startswith("root/"), target
r=patch(source2,target["path"],"hq")
assert r["statementDefEq"] and r["proofShapePreserved"] and r["status"]=="checked",r
assert any(d["name"]=="hq" and d["type"]=="Q" and d["matchesGoal"] for d in target["scope"]), target
assert not any(d["name"]=="hp" and d["matchesGoal"] for d in target["scope"]), target
assert any(a["function"]=="hpq" and a["argument"]=="hp" for a in target["applications"]),target
noop=patch(source2,target["path"],"hpq hp")
assert noop["unchanged"] and noop["source"]==source2,noop
assert "hqr hq" in r["source"],r
for invalid in ["hp", "unknownVariable", "by sorry"]:
    try:
        patch(source2,target["path"],invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("Invalid replacement accepted: "+invalid)
print("Typed replacement, standalone recompilation, statement comparison and rejection passed")

same_type = """theorem same_type (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
target=next(n for n in walk(extract(same_type)["tree"]) if n["kind"]=="hypothesis" and n["term"]=="h1")
r=patch(same_type,target["path"],"h2")
assert r["proofShapePreserved"] and not r["unchanged"],r
assert "h2" in r["source"],r
print("Same-proposition assumptions retain their distinct proof occurrences; no-op preserves source")

source3 = """theorem witness_example : ∃ n : Nat, True := by
  exact ⟨0, True.intro⟩
"""
w=next(n for n in walk(extract(source3)["tree"]) if n["kind"]=="witness")
assert w["type"]=="Nat" and w["editable"],w
r=patch(source3,w["path"],"1")
assert r["proofShapePreserved"] and not r["unchanged"],r

dependent = """theorem dependent_witness : ∃ n : Nat, n = 0 := by
  exact ⟨0, rfl⟩
"""
w=next(n for n in walk(extract(dependent)["tree"]) if n["kind"]=="witness")
try:
    patch(dependent,w["path"],"1")
except ValueError:
    pass
else:
    raise AssertionError("Invalid dependent witness accepted")

quantified = """theorem quantified (P : Nat → Prop) (h : ∀ n : Nat, P n) (a : Nat) : P a := by
  exact h a
"""
q=next(n for n in walk(extract(quantified)["tree"]) if n.get("reference")=="h" and n["kind"]=="apply")
assert any(a["function"]=="h" and a["argument"]=="a" for a in q["applications"]),q
print("Dependent applications and existential witness replacement/rejection passed")

pair_source = """theorem witness_pair : ∃ n : Nat, n = n := by
  exact ⟨0, rfl⟩
"""
pair_node=next(n for n in walk(extract(pair_source)["tree"]) if n.get("reference")=="Exists.intro")
single=next(n for n in pair_node["children"] if n["kind"]=="witness")
try:
    patch(pair_source,single["path"],"1")
except ValueError:
    pass
else:
    raise AssertionError("Stale equality evidence accepted after witness change")
r=patch(pair_source,pair_node["path"],"Exists.intro (1 : Nat) rfl")
assert r["proofShapePreserved"] and r["statementDefEq"] and not r["unchanged"],r
print("Atomic dependent witness/evidence replacement passed")


# Direct syntactic occurrences distinguish hypotheses even when their types coincide.
dep_source = """theorem dependency_example (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
dep_node=next(n for n in walk(extract(dep_source)["tree"]) if n["kind"]=="hypothesis" and n["term"]=="h1")
scope={d["name"]:d for d in dep_node["scope"]}
assert scope["h1"]["usedInTerm"] and not scope["h2"]["usedInTerm"],scope
assert scope["P"]["usedInType"] and not scope["h1"]["usedInType"],scope
print("Direct expression dependencies preserve distinct local hypotheses")
