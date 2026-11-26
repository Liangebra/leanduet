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
assert r["statementDefEq"] and r["status"]=="checked",r
assert "hqr hq" in r["source"],r
for invalid in ["hp", "unknownVariable", "by sorry"]:
    try:
        patch(source2,target["path"],invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("Invalid replacement accepted: "+invalid)
print("Typed replacement, standalone recompilation, statement comparison and rejection passed")
