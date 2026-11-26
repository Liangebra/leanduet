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
