"""Multi-theorem document inventory, selection and checked final edit."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import document_info,document_extract,document_patch
source="""theorem first (P : Prop) (h : P) : P := by
  exact h

theorem second (P : Prop) (h1 h2 : P) : P := by
  exact first P h1
"""
d=document_info(source)
assert [r["name"] for r in d["declarations"]]==["first","second"],d
assert d["declarations"][1]["dependencies"]==["first"],d
assert not d["declarations"][0]["editable"] and d["declarations"][1]["editable"],d
def walk(n):
    yield n
    for c in n["children"]: yield from walk(c)
node=next(n for n in walk(document_extract(source,"second")["tree"]) if n.get("reference")=="first")
r=document_patch(source,"second",node["path"],"h2")
assert r["source"].startswith(source[:source.index("theorem second")]),r
assert r["proofShapePreserved"] and r["statementDefEq"] and r["prefixPreserved"],r
assert document_info(r["source"])["declarations"][1]["dependencies"]==[],r
try:
    document_patch(source,"first","root","by assumption")
except ValueError: pass
else: raise AssertionError("Earlier declaration unexpectedly editable")
print("Verified document graph and final theorem edit")
