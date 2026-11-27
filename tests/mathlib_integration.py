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
from semantic import infer_chain

project=Path(sys.argv[1]).resolve()
mathlib_cases=json.loads((Path(__file__).resolve().parent/"fixtures"/"mathlib-cases.json").read_text(encoding="utf-8"))
mathlib_case=next(case for case in mathlib_cases if case["id"]=="compact-image-continuous")
source=mathlib_case["leanImport"]+"\n\n"+mathlib_case["leanTheoremHeader"]+" := "+mathlib_case["leanProofBody"]+"\n"

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
nested=source.replace("theorem compact_image_example","theorem compact_image_refactor").replace(
    mathlib_case["goal"]+" := "+mathlib_case["leanProofBody"],
    mathlib_case["goal"]+" ∧ True := by\n  exact ⟨IsCompact.image hs hf, True.intro⟩")
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
const example="""+json.dumps(mathlib_case,ensure_ascii=False)+r""";
const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
if(!result.complete||result.rows.at(-1).proofStatus!=='candidate'||result.steps.at(-1).application!==example.expectedStructure[0].application)throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
term=json.loads(subprocess.run(["node","--input-type=module"],input=draft_script,text=True,cwd=root,check=True,capture_output=True).stdout)
generated=mathlib_case["leanImport"]+"\n\n"+mathlib_case["leanTheoremHeader"].replace("compact_image_example","compact_image_from_natural")+" := "+term+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"CompactImageFromNatural.lean"
    target.write_text(generated,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
print("Mathlib topology: natural-draft compact-image candidate accepted by Lean")
natural_tree=extract(generated,project)["tree"]
natural_node=next(n for n in walk(natural_tree) if n.get("reference")=="IsCompact.image")
needed=[d for d in natural_node["scope"] if d["neededForContext"]]
needed_names={d["name"] for d in needed}
assert set(mathlib_case["expectedContextClosure"]).issubset(needed_names),needed
for instance in mathlib_case["requiredTypeclassClosure"]:
    assert any(instance in d["type"] for d in needed),needed
print("Mathlib topology: extracted proof retains its dependent data and topology-instance closure")

# Exercise a child proof scope with a real proposition and theorem family. The
# Lean backend must return only the local lemma binding to its parent frame.
lemma_steps=[{
    "kind":"local-lemma","name":"himage","type":"IsCompact (f '' s)",
    "subgoals":[{"id":"proof","goal":"IsCompact (f '' s)","steps":[{
        "kind":"conclude","type":"IsCompact (f '' s)","application":"IsCompact.image hs hf"
    }]}]
},{"kind":"conclude","type":"IsCompact (f '' s)","application":"himage"}]
backend_lemma=infer_chain(source,node["path"],lemma_steps,project)
assert [binding["name"] for binding in backend_lemma["bindings"]]==["himage"],backend_lemma
assert backend_lemma["goal"]=="IsCompact (f '' s)",backend_lemma

local_draft_script=r"""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const example="""+json.dumps(mathlib_case,ensure_ascii=False)+r""";
const result=compileNaturalDraft(example.localLemmaDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
if(!result.complete||result.steps[0]?.kind!=='local-lemma')throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
local_term=json.loads(subprocess.run(["node","--input-type=module"],input=local_draft_script,text=True,cwd=root,check=True,capture_output=True).stdout)
local_declaration=mathlib_case["leanImport"]+"\n\n"+mathlib_case["leanTheoremHeader"].replace("compact_image_example","compact_image_local_lemma")+" := "+local_term+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"CompactImageLocalLemma.lean"
    target.write_text(local_declaration,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
print("Mathlib topology: browser and backend local-lemma candidates compile with scoped dependencies")
