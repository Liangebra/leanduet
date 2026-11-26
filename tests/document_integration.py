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
assert all(r["editable"] for r in d["declarations"]),d
assert d["declarations"][0]["transitiveDependents"]==["second"],d
def walk(n):
    yield n
    for c in n["children"]: yield from walk(c)
node=next(n for n in walk(document_extract(source,"second")["tree"]) if n.get("reference")=="first")
r=document_patch(source,"second",node["path"],"h2")
assert r["source"].startswith(source[:source.index("theorem second")]),r
assert r["proofShapePreserved"] and r["statementDefEq"] and r["prefixPreserved"],r
assert document_info(r["source"])["declarations"][1]["dependencies"]==[],r
source2="""theorem first (P : Prop) (h1 h2 : P) : P := by
  exact h1

theorem second (P : Prop) (h1 h2 : P) : P := by
  exact first P h1 h2

theorem third (P : Prop) (h1 h2 : P) : P := by
  exact second P h1 h2
"""
d=document_info(source2)
assert d["declarations"][2]["transitiveDependencies"]==["first","second"],d
assert d["declarations"][0]["transitiveDependents"]==["second","third"],d
target=next(n for n in walk(document_extract(source2,"first")["tree"]) if n.get("term")=="h1" and n.get("kind")=="hypothesis")
r=document_patch(source2,"first",target["path"],"h2")
assert r["otherDeclarationsPreserved"] and r["checkedOtherDeclarations"]==["second","third"],r
assert r["source"].endswith(source2[source2.index("theorem second"):]),r
print("Earlier theorem edit preserves all other declaration structures and transitive dependencies")

assert source2[d["declarations"][0]["start"]:d["declarations"][0]["end"]].startswith("theorem first"),d
assert source2[d["declarations"][0]["end"]:d["declarations"][1]["start"]].strip()=="",d
try:
    document_info(source2.replace("\ntheorem second","\n  def hidden := 1\n\ntheorem second"))
except ValueError: pass
else: raise AssertionError("An extra command was incorrectly accepted within a declaration range")
print("Native Lean ranges validate the restricted source boundaries")
