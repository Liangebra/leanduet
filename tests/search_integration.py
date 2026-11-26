"""Actual local and library search; no AI, no Mathlib installation required."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract, search, patch

def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)

source="""theorem reversed (a b : Nat) (h : a = b) : b = a := by
  exact Eq.symm h
"""
node=next(n for n in walk(extract(source)["tree"]) if n.get("reference")=="Eq.symm")
result=search(source,node["path"],"Eq.symm")
assert result["candidates"],result
assert any(c["rule"]=="Eq.symm" for c in result["candidates"]),result
assert patch(source,node["path"],result["candidates"][0]["term"])["proofShapePreserved"]
assert search(source,node["path"],"Unknown.not_here")["candidates"]==[]
assert search(source,node["path"],"reversed")["candidates"]==[]

source2="""theorem chain (P Q R : Prop) (f : P → Q) (g : Q → R) (p : P) : R := by
  exact g (f p)
"""
node=next(n for n in walk(extract(source2)["tree"]) if n.get("reference")=="g")
r=search(source2,node["path"])
assert r["candidates"],r
assert any(c["rule"]=="local elimination" for c in r["candidates"]),r
assert patch(source2,node["path"],r["candidates"][0]["term"])["statementDefEq"]
print("Typed library application, multi-step local elimination, and self-reference rejection passed")


trans_source="""theorem trans_chain (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  exact Eq.trans hab hbc
"""
node=next(n for n in walk(extract(trans_source)["tree"]) if n.get("reference")=="Eq.trans")
r=search(trans_source,node["path"],"Eq.trans",required=["hab","hbc"])
assert r["candidates"],r
assert any("hab" in c["term"] and "hbc" in c["term"] for c in r["candidates"]),r
try:
    search(trans_source,node["path"],"Eq.trans",required=["notInScope"])
except ValueError:
    pass
else:
    raise AssertionError("An unresolved named premise was accepted")
print("Controlled rule intent preserves the named local premises")
