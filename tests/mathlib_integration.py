"""Integration against Mathlib 4.19, in an independently built Lake project.
Usage: python tests/mathlib_integration.py /path/to/mathlib4
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract, search, patch, inspect_ir, abstract_preview, factor_preview

project=Path(sys.argv[1]).resolve()
source="""import Mathlib.Topology.Compactness.Compact

theorem compact_image_example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : X → Y) (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  exact IsCompact.image hs hf
"""

def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)

tree=extract(source,project)["tree"]
node=next(n for n in walk(tree) if n.get("reference")=="IsCompact.image")
result=search(source,node["path"],"IsCompact.image",project)
assert result["candidates"],result
candidate=next(c for c in result["candidates"] if c["rule"]=="IsCompact.image")
r=patch(source,node["path"],candidate["term"],project)
assert r["statementDefEq"] and r["proofShapePreserved"],r
print("Mathlib topology: compactness-preserving continuous image retrieved and checked")

# A real Mathlib theorem with dependent instance parameters, rather than
# an isolated propositional example. The inner compact-image proof is
# extracted from an enclosing conjunction, keeping its outer constructor.
nested=source.replace("theorem compact_image_example","theorem compact_image_refactor").replace("IsCompact (f '' s) := by\n  exact IsCompact.image hs hf","IsCompact (f '' s) ∧ True := by\n  exact ⟨IsCompact.image hs hf, True.intro⟩")
inner=next(n for n in walk(extract(nested,project)["tree"]) if n.get("reference")=="IsCompact.image")
ir=inspect_ir(nested,inner["path"],project=project)
assert ir["judgment"]["roundTrip"]["freshContextChecked"],ir
a=abstract_preview(nested,inner["path"],project)
assert a["closedChecked"] and a["reopenedShape"],a
assert a["standaloneChecked"] and a["exportShapePreserved"],a
r=factor_preview(nested,inner["path"],project)
assert r["standaloneChecked"] and r["lemmaShapePreserved"] and r["proofComplementPreserved"],r
assert "LeanDuetExtractedLemma" in r["source"],r
print("Mathlib topology: dependent-context round trip and nested compact-image factoring checked")
