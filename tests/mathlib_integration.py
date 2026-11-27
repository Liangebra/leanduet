"""Integration against Mathlib 4.19, in an independently built Lake project.
Usage: python tests/mathlib_integration.py /path/to/mathlib4
"""
from pathlib import Path
import sys
import json
import subprocess
from tempfile import TemporaryDirectory
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

print('Checking semantic adapter under Mathlib syntax extensions',flush=True)
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

# Exercise the same bounded natural-language candidate against the real
# Mathlib theorem signature. Candidate generation is structural; this fresh
# declaration is accepted only after Mathlib's Lean elaborator checks it.
root=Path(__file__).resolve().parents[1]
draft_script=r"""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['hs','IsCompact s'],['hf','Continuous f']]);
const input=String.raw`因此 $IsCompact (f '' s)$，由紧集的连续像，使用 hs 和 hf`;
const result=compileNaturalDraft(input,['f','s','hs','hf'],facts,{goal:"IsCompact (f '' s)"});
if(!result.complete||result.rows.at(-1).proofStatus!=='candidate')throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
term=json.loads(subprocess.run(["node","--input-type=module"],input=draft_script,text=True,cwd=root,check=True,capture_output=True).stdout)
generated="""import Mathlib.Topology.Compactness.Compact

theorem compact_image_from_natural (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : X → Y) (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := """+term+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"CompactImageFromNatural.lean"
    target.write_text(generated,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
print("Mathlib topology: natural-draft compact-image candidate accepted by Lean")
natural_tree=extract(generated,project)["tree"]
natural_node=next(n for n in walk(natural_tree) if n.get("reference")=="IsCompact.image")
needed=[d for d in natural_node["scope"] if d["neededForContext"]]
needed_names={d["name"] for d in needed}
assert {"X","Y","s","f","hs","hf"}.issubset(needed_names),needed
for space in ("X","Y"):
    assert any("TopologicalSpace "+space in d["type"] for d in needed),needed
print("Mathlib topology: extracted proof retains its dependent data and topology-instance closure")
