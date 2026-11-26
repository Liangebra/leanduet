"""Integration against Mathlib 4.19, in an independently built Lake project.
Usage: python tests/mathlib_integration.py /path/to/mathlib4
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract, search, patch

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
