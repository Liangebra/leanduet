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

# This second corpus case crosses from topology to abstract algebra. The prose
# names the subgroup closure rule and supplies its two membership premises;
# the goal, data dependencies, and theorem application are checked separately.
subgroup_case=next(case for case in mathlib_cases if case["id"]=="subgroup-multiplication-closure")
subgroup_script=r"""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const example="""+json.dumps(subgroup_case,ensure_ascii=False)+r""";
const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
if(!result.complete||result.steps.at(-1)?.application!=="Subgroup.mul_mem H hx hy")throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
subgroup_term=json.loads(subprocess.run(["node","--input-type=module"],input=subgroup_script,text=True,cwd=root,check=True,capture_output=True).stdout)
subgroup_source=subgroup_case["leanImport"]+"\n\n"+subgroup_case["leanTheoremHeader"].replace(
    "subgroup_mul_closure_example","subgroup_mul_closure_from_natural")+" := "+subgroup_term+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"SubgroupMulClosure.lean"
    target.write_text(subgroup_source,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
print("Mathlib algebra: subgroup multiplication candidate accepted by Lean")

subgroup_tree=extract(subgroup_source,project)["tree"]
subgroup_node=next(n for n in walk(subgroup_tree) if n.get("reference")=="Subgroup.mul_mem")
subgroup_needed=[d for d in subgroup_node["scope"] if d["neededForContext"]]
needed_names={d["name"] for d in subgroup_needed}
assert {"G","H","x","y","hx","hy"}.issubset(needed_names),subgroup_needed
assert any("Group G" in d["type"] for d in subgroup_needed),subgroup_needed
print("Mathlib algebra: proof dependency view retains group structure, subgroup, objects, and membership facts")

# This linear-algebra case exercises a user-facing concept alias, a checked
# Mathlib declaration, the transitive module-instance context, and an edit
# whose new surface proposition is compared against a full cold compilation.
linear_case=next(case for case in mathlib_cases if case["id"]=="linear-map-additivity")
linear_script=r"""
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession} from './web/natural-draft.mjs';
const example="""+json.dumps(linear_case,ensure_ascii=False)+r""";
const scope=example.scope;
const context=new Map(Object.entries(example.context));
const session=createDraftSession();
const first=session.evaluate(example.naturalDraft,scope,context,{goal:example.goal});
if(!first.complete||first.steps.at(-1)?.application!==example.expectedStructure[0].application)throw new Error(JSON.stringify(first));
const edited=session.evaluate(example.editedNaturalDraft,scope,context,{goal:example.editedGoal});
const cold=compileNaturalDraft(example.editedNaturalDraft,scope,context,{goal:example.editedGoal});
const stripReuse=({reusedRows,...result})=>result;
assert.deepEqual(stripReuse(edited),stripReuse(cold));
if(!edited.complete||edited.steps.at(-1)?.application!==example.editedExpectedStructure[0].application)throw new Error(JSON.stringify(edited));
console.log(JSON.stringify({term:first.term,editedTerm:edited.term}));
"""
linear_process=subprocess.run(["node","--input-type=module"],input=linear_script,text=True,cwd=root,check=False,capture_output=True)
if linear_process.returncode:
    print(linear_process.stdout)
    print(linear_process.stderr,file=sys.stderr)
    raise SystemExit(linear_process.returncode)
linear_terms=json.loads(linear_process.stdout)
linear_source=linear_case["leanImport"]+"\n\n"+linear_case["leanTheoremHeader"].replace(
    "linear_map_add_example","linear_map_add_from_natural")+" := "+linear_terms["term"]+"\n"
edited_header=linear_case["leanTheoremHeader"].replace("linear_map_add_example","linear_map_add_edited").replace(
    linear_case["goal"],linear_case["editedGoal"])
edited_source=linear_case["leanImport"]+"\n\n"+edited_header+" := "+linear_terms["editedTerm"]+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"LinearMapAddFromNatural.lean"
    target.write_text(linear_source,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
    edited_target=Path(tmp)/"LinearMapAddEdited.lean"
    edited_target.write_text(edited_source,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(edited_target)],cwd=project,check=True)
print("Mathlib linear algebra: original and variable-order edit candidates compile")

linear_tree=extract(linear_source,project)["tree"]
linear_node=next((n for n in walk(linear_tree) if n.get("reference","").split(".")[-1]=="map_add"),None)
assert linear_node,linear_tree
linear_needed=[d for d in linear_node["scope"] if d["neededForContext"]]
needed_names={d["name"] for d in linear_needed}
assert set(linear_case["expectedContextClosure"]).issubset(needed_names),linear_needed
for instance in linear_case["requiredTypeclassClosure"]:
    assert any(instance in d["type"] for d in linear_needed),(instance,linear_needed)
print("Mathlib linear algebra: proof dependency view retains map, variables, and module structure")

# The composition rule exercises function-composition syntax in the shared
# mathematical AST and retains all three topology structures in Lean context.
composition_case=next(case for case in mathlib_cases if case["id"]=="continuous-function-composition")
composition_script=r"""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const example="""+json.dumps(composition_case,ensure_ascii=False)+r""";
const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
if(!result.complete||result.rows.at(-1).proofStatus!=='candidate'||result.steps.at(-1)?.application!=="Continuous.comp hg hf")throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
composition_term=json.loads(subprocess.run(["node","--input-type=module"],input=composition_script,text=True,cwd=root,check=True,capture_output=True).stdout)
composition_source=composition_case["leanImport"]+"\n\n"+composition_case["leanTheoremHeader"].replace(
    "continuous_comp_example","continuous_comp_from_natural")+" := "+composition_term+"\n"
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"ContinuousCompositionFromNatural.lean"
    target.write_text(composition_source,encoding="utf-8")
    subprocess.run(["lake","env","lean",str(target)],cwd=project,check=True)
print("Mathlib topology: continuous-composition candidate accepted by Lean")
composition_tree=extract(composition_source,project)["tree"]
composition_node=next(n for n in walk(composition_tree) if n.get("reference")=="Continuous.comp")
composition_needed=[d for d in composition_node["scope"] if d["neededForContext"]]
composition_names={d["name"] for d in composition_needed}
assert set(composition_case["expectedContextClosure"]).issubset(composition_names),composition_needed
for instance in composition_case["requiredTypeclassClosure"]:
    assert any(instance in d["type"] for d in composition_needed),(instance,composition_needed)
print("Mathlib topology: composition dependency view retains both functions and all three topology instances")

# Issue #9: a real proof-refactoring counterexample. Both declarations state
# the same Mathlib proposition. The direct subterm uses h2, not the distinct
# same-typed h1; the local-let version changes the elaborated term structure.
counterexample_path=Path(__file__).resolve().parent/"mathlib"/"ProofRefactorCounterexamples.lean"
counterexample_source=counterexample_path.read_text(encoding="utf-8")
subprocess.run(["lake","env","lean",str(counterexample_path)],cwd=project,check=True)
direct_marker="\ntheorem compact_image_refactor_direct"
let_marker="\ntheorem compact_image_refactor_local_let"
assert direct_marker in counterexample_source and let_marker in counterexample_source
direct_start=counterexample_source.index(direct_marker)
let_start=counterexample_source.index(let_marker)
shared_prefix=counterexample_source[:direct_start]
direct_source=shared_prefix+counterexample_source[direct_start:let_start]
local_let_source=shared_prefix+counterexample_source[let_start:]
direct_tree=extract(direct_source,project)["tree"]
local_let_tree=extract(local_let_source,project)["tree"]
assert direct_tree["type"]==local_let_tree["type"],(direct_tree,local_let_tree)
assert any(n["kind"]=="let" and n.get("binder")=="imageProof" for n in walk(local_let_tree)),local_let_tree
assert not any(n["kind"]=="let" and n.get("binder")=="imageProof" for n in walk(direct_tree)),direct_tree

direct_node=next(n for n in walk(direct_tree) if n.get("reference")=="IsCompact.image")
direct_scope={d["name"]:d for d in direct_node["scope"]}
assert direct_scope["h1"]["type"]==direct_scope["h2"]["type"],direct_scope
assert direct_scope["h2"]["neededForContext"],direct_scope
assert not direct_scope["h1"]["neededForContext"],direct_scope
assert {"s","f","h2","hf"}.issubset({name for name,d in direct_scope.items() if d["neededForContext"]}),direct_scope

let_node=next(n for n in walk(local_let_tree) if n["kind"]=="let" and n.get("binder")=="imageProof")
let_value=next(n for n in walk(let_node["children"][0]) if n.get("reference")=="IsCompact.image")
let_scope={d["name"]:d for d in let_value["scope"]}
assert let_scope["h1"]["type"]==let_scope["h2"]["type"],let_scope
assert let_scope["h2"]["neededForContext"] and not let_scope["h1"]["neededForContext"],let_scope
print("Mathlib refactoring counterexample: same-typed premise identity and local-let term shape checked")
