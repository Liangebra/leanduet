from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract,interpret
source="""theorem choice (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
def walk(n):
    yield n
    for c in n["children"]: yield from walk(c)
node=next(n for n in walk(extract(source)["tree"]) if n.get("term")=="h1")
r=interpret(source,node["path"],[
 {"formula":"P","term":"h2","required":["h2"]},
 {"formula":"False","term":"h1"},
 {"term":"h1","required":["h2"]},
 {"formula":"P","term":"h1"}])
assert [x["status"] for x in r["interpretations"]]==["locally-checked","rejected","rejected","locally-checked"],r
assert r["interpretations"][0]["candidates"][0]["term"]=="h2",r
print("Multiple local interpretations checked independently; wrong goals and unused premises rejected")

# Exercise the actual JavaScript translation, not a hand-written Lean term.
import json
import subprocess
from tempfile import TemporaryDirectory

root = Path(__file__).resolve().parents[1]
script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['P','Nat → Prop'],['s','List Nat'],['a','Nat'],['h','∀ x, x ∈ s → P x'],['hm','a ∈ s']]);
const input='建立 hp : $P(a)$，由 h、a、hm\\n由 a、hm、hp 得到 $∃ x ∈ s, P(x)$';
const r=compileNaturalDraft(input,[...facts.keys()],facts);
console.log(JSON.stringify(r.term));
"""
term = json.loads(subprocess.run(["node", "--input-type=module"], input=script, text=True, cwd=root, check=True, capture_output=True).stdout)
assert "h a hm" in term and "Exists.intro a (And.intro hm hp)" in term, term
with TemporaryDirectory() as tmp:
    target = Path(tmp) / "Generated.lean"
    target.write_text("theorem bounded (P : Nat → Prop) (s : List Nat) (a : Nat) (h : ∀ x, x ∈ s → P x) (hm : a ∈ s) : ∃ x, x ∈ s ∧ P x := " + term + "\n", encoding="utf-8")
    subprocess.run(["lean", str(target)], cwd=root, check=True)
print("JavaScript-generated bounded quantifier proof accepted by Lean")

# Compile context extensions independently; use the actual generated source.
extension_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const goal='∀ z : Nat, P z → P z';
const a=compileNaturalDraft('任取 x : $Nat$\\n假设 hp : $P(x)$\\n$P(x)$ | hp',['P'],new Map(),{goal});
const b=compileNaturalDraft('令 y : $Nat$ := $f(x)$\\n由 h 与 y 得到 $P(y)$',['P','f','x','h'],new Map([['f','Nat → Nat'],['x','Nat'],['h','∀ z : Nat, P z']]));
console.log(JSON.stringify([a.term,b.term]));
"""
intro_term, let_term = json.loads(subprocess.run(["node", "--input-type=module"], input=extension_script, text=True, cwd=root, check=True, capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target = Path(tmp) / "ContextExtensions.lean"
    target.write_text(
        "theorem intro_demo (P : Nat → Prop) : ∀ z : Nat, P z → P z := " + intro_term + "\n"
        "theorem let_demo (P : Nat → Prop) (f : Nat → Nat) (x : Nat) (h : ∀ z : Nat, P z) : P (f x) := " + let_term + "\n",
        encoding="utf-8")
    subprocess.run(["lean", str(target)], cwd=root, check=True)
print("Generated local definitions and context introductions accepted by Lean")


# The omitted proposition is determined by a later statement, not by the
# order of the conjunction's arguments. Both resulting fragments compile.
constraint_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['h','P ∧ Q'],['f','P → R'],['g','Q → R']]);
const prefix='建立 hp : $?$,由 h\\n';
console.log(JSON.stringify(['f','g'].map(rule=>compileNaturalDraft(prefix+'由 hp 与 '+rule+' 得到 $R$',[...facts.keys()],facts).term)));
"""
left_term, right_term = json.loads(subprocess.run(["node", "--input-type=module"], input=constraint_script, text=True, cwd=root, check=True, capture_output=True).stdout)
assert "And.left h" in left_term and "And.right h" in right_term
with TemporaryDirectory() as tmp:
    target = Path(tmp) / "Constrained.lean"
    signature = " (P Q R : Prop) (h : P ∧ Q) (f : P → R) (g : Q → R) : R := "
    target.write_text("theorem constrained_left" + signature + left_term + "\n"
                      "theorem constrained_right" + signature + right_term + "\n", encoding="utf-8")
    subprocess.run(["lean", str(target)], cwd=root, check=True)
print("Both backward-constrained proof fragments accepted by Lean")

# The two independent holes have correlated choices. Both legal assignments
# must compile; inconsistent assignments must not be exported.
joint_script = """
import {draftProof,compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['h','P ∧ Q'],['k','(P → R) ∧ (Q → R)']]);
const input='建立 hp : $?$,由 h\\n建立 hf : $?$,由 k\\n由 hp 与 hf 得到 $R$';
const scope=[...facts.keys()];
const left=compileNaturalDraft(input,scope,facts,{choices:new Map([[2,'And.left k']])});
const right=compileNaturalDraft(input,scope,facts,{choices:new Map([[2,'And.right k']])});
const bad=draftProof(input,scope,facts,{choices:new Map([[1,'And.left h'],[2,'And.right k']])});
console.log(JSON.stringify([left.term,right.term,bad.term,bad.graph.constraintGroups[0].status]));
"""
joint_left,joint_right,joint_bad,joint_status=json.loads(subprocess.run(["node","--input-type=module"],input=joint_script,text=True,cwd=root,check=True,capture_output=True).stdout)
assert joint_bad is None and joint_status=="contradiction"
assert "And.left h" in joint_left and "And.left k" in joint_left
assert "And.right h" in joint_right and "And.right k" in joint_right
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"JointConstraints.lean"
    signature=" (P Q R : Prop) (h : P ∧ Q) (k : (P → R) ∧ (Q → R)) : R := "
    target.write_text("theorem joint_left"+signature+joint_left+"\n"+"theorem joint_right"+signature+joint_right+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Both correlated proof assignments accepted by Lean; conflicting assignment not exported")

# Conditional projection types: the very same child Lean term can denote a
# proof of P or R, depending on the earlier type. Validate both directions.
dependent_script = """
import {compileNaturalDraft,draftProof} from './web/natural-draft.mjs';
const facts=new Map([['h','(P ∧ Q) ∧ (R ∧ S)'],['f','P → T'],['g','R → T']]);
const scope=[...facts.keys()];
const prefix='建立 hu : $?$,由 h\\n建立 hv : $?$,由 hu\\n';
const left=compileNaturalDraft(prefix+'由 hv 与 f 得到 $T$',scope,facts);
const right=compileNaturalDraft(prefix+'由 hv 与 g 得到 $T$',scope,facts);
const bad=draftProof(prefix+'由 hv 与 g 得到 $T$',scope,facts,{choices:new Map([[1,'And.left h']])});
console.log(JSON.stringify([left.term,right.term,bad.term]));
"""
dep_left,dep_right,dep_bad=json.loads(subprocess.run(["node","--input-type=module"],input=dependent_script,text=True,cwd=root,check=True,capture_output=True).stdout)
assert dep_bad is None
assert "And.left h" in dep_left and "And.right h" in dep_right
assert "And.left hu" in dep_left and "And.left hu" in dep_right
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"DependentConstraints.lean"
    signature=" (P Q R S T : Prop) (h : (P ∧ Q) ∧ (R ∧ S)) (f : P → T) (g : R → T) : T := "
    target.write_text("theorem dependent_left"+signature+dep_left+"\n"+"theorem dependent_right"+signature+dep_right+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Both conditional projection types accepted by Lean; incompatible source not exported")

quantified_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const a=compileNaturalDraft('任取 x\\n假设 hx\\n$P(x)$ | hx',['P'],new Map(),{goal:'∀ z : Nat, P z → P z'});
const facts=new Map([['h','∃ z : Nat, P z'],['f','∀ z : Nat, P z → R']]);
const b=compileNaturalDraft('由 h 取 x，记 hx\\n由 f、x、hx 得到 $R$',['P','R',...facts.keys()],facts);
const c=compileNaturalDraft('由 h 取 x，记 hx\\n$∃ z : Nat, P(z)$ | h',['P','h'],new Map([['h','∃ z : Nat, P z']]));
console.log(JSON.stringify([a.term,b.term,c.term]));
"""
implicit_term, obtain_term, preserve_term=json.loads(subprocess.run(["node","--input-type=module"],input=quantified_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"QuantifiedContext.lean"
    target.write_text("import Lean\n"
        +"theorem implicit_intro (P : Nat → Prop) : ∀ z : Nat, P z → P z := "+implicit_term+"\n"
        +"theorem obtain_demo (P : Nat → Prop) (R : Prop) (h : ∃ z : Nat, P z) (f : ∀ z : Nat, P z → R) : R := "+obtain_term+"\n"
        +"theorem preserve_exists (P : Nat → Prop) (h : ∃ z : Nat, P z) : ∃ z : Nat, P z := "+preserve_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Implicit introductions and existential elimination accepted by Lean")

operation_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const propositionFacts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]);
const arbitrary=compileNaturalDraft('take an element x satisfying $P(x)$\\n$P(x)$ | hall x',
 ['hall','he'],propositionFacts,{goal:'∀ x : Nat, P x'});
const existentialFacts=new Map([['he','∃ y : Nat, P y'],['hq','Q']]);
const witness=compileNaturalDraft('take an element x satisfying $P(x)$ from he\\n$Q$ | hq',
 ['he','hq'],existentialFacts,{goal:'Q'});
console.log(JSON.stringify([arbitrary.term,witness.term]));
"""
arbitrary_term, witness_term = json.loads(subprocess.run(["node", "--input-type=module"], input=operation_script, text=True, cwd=root, check=True, capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target = Path(tmp) / "ElementOperations.lean"
    target.write_text(
        "theorem arbitrary_element (P : Nat → Prop) (hall : ∀ x : Nat, P x) (he : ∃ y : Nat, P y) : ∀ x : Nat, P x := " + arbitrary_term + "\n"
        "theorem extract_element (P : Nat → Prop) (Q : Prop) (he : ∃ y : Nat, P y) (hq : Q) : Q := " + witness_term + "\n",
        encoding="utf-8")
    subprocess.run(["lean", str(target)], cwd=root, check=True)
print("Selected universal and existential readings of an element request accepted by Lean")

# Exercise the structured backend as well as standalone rendered Lean.
from semantic import infer_chain,patch
obtain_source="theorem backend_obtain (P : Nat → Prop) (R : Prop) (h : ∃ z : Nat, P z) (f : ∀ z : Nat, P z → R) : R := by\n  exact Exists.elim h f\n"
# Select the proof occurrence by its actual elaborated local goal and scope.
nodes=list(walk(extract(obtain_source)["tree"]))
obtain_node=next(n for n in nodes if n.get("type")=="R" and {"P","R","h","f"}.issubset({d.get("name") for d in n.get("scope",[])}))
backend=infer_chain(obtain_source,obtain_node["path"],[
    {"kind":"obtain","source":"h","copy":"duet_exists_x","name":"x","evidenceName":"hx","type":"Nat","evidenceType":"P x"},
    {"kind":"conclude","type":"R","application":"f x hx"}])
assert [b["name"] for b in backend["bindings"]]==["x","hx"],backend
print("Structured existential chain elaborates and traces both bindings")

# Nested disjunction elimination preserves branch-local names, while the
# structured Lean backend exports only the common result to the parent scope.
case_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['R','Prop'],['h','P ∨ Q'],['j','U ∨ V'],['f','P → U → R'],['g','P → V → R'],['k','Q → R']]);
const input='分情况讨论 h，建立 hR : $R$\\n  左支 hp\\n    分情况讨论 j，建立 hpR : $R$\\n      左支 hu\\n        $R$ | f hp hu\\n      右支 hv\\n        $R$ | g hp hv\\n    $R$ | hpR\\n  右支 hq\\n    $R$ | k hq\\n$R$ | hR';
console.log(JSON.stringify(compileNaturalDraft(input,[...facts.keys()],facts,{goal:'R'}).steps));
"""
case_steps=json.loads(subprocess.run(["node","--input-type=module"],input=case_script,text=True,cwd=root,check=True,capture_output=True).stdout)
case_source="""theorem nested_disjunction (P Q U V R : Prop) (h : P ∨ Q) (j : U ∨ V)
    (f : P → U → R) (g : P → V → R) (k : Q → R) : R := by
  cases h with
  | inl hp =>
    cases j with
    | inl hu => exact f hp hu
    | inr hv => exact g hp hv
  | inr hq => exact k hq
"""
case_node=next(n for n in walk(extract(case_source)["tree"]) if n.get("type")=="R" and {"P","Q","U","V","R","h","j","f","g","k"}.issubset({d.get("name") for d in n.get("scope",[])}))
case_backend=infer_chain(case_source,case_node["path"],case_steps)
assert [b["name"] for b in case_backend["bindings"]]==["hR"],case_backend
assert "hpR" not in [b["name"] for b in case_backend["bindings"]]
assert "cases j with" in case_backend["term"] and "exact hR" in case_backend["term"]
case_preview=patch(case_source,case_node["path"],case_backend["term"])
assert case_preview["status"]=="checked" and case_preview["proofShapePreserved"]
try:
    infer_chain(case_source,case_node["path"],[case_steps[0],{"kind":"conclude","type":"R","application":"hp"}])
    raise AssertionError("a branch-local hypothesis escaped its case scope")
except ValueError:
    pass
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"NestedDisjunction.lean"
    target.write_text("theorem generated_nested (P Q U V R : Prop) (h : P ∨ Q) (j : U ∨ V) (f : P → U → R) (g : P → V → R) (k : Q → R) : R := "+case_backend["term"]+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Nested branch-local case elimination elaborates in the structured backend; only the common result escapes")

# A top-level proof may interleave ordinary local facts with several separate
# scoped case blocks. Verify the combined candidate rather than only its JS AST.
sequence_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['R','Prop'],['T','Prop'],
 ['h','P ∨ Q'],['j','U ∨ V'],['p','P'],['f','P → R'],['g','P → T'],['k','Q → T'],['l','U → T'],['m','V → T']]);
const input='establish hr : $R$ | f p\\n'+
 'cases h, establish hT : $T$\\n  left case hp\\n    $T$ | g hp\\n  right case hq\\n    $T$ | k hq\\n'+
 'establish ht : $T$ | hT\\n'+
 'cases j, establish jT : $T$\\n  left case hu\\n    $T$ | l hu\\n  right case hv\\n    $T$ | m hv\\n'+
 '$T$ | jT';
const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'T'});
if(!result.complete||result.graph.nodes.filter(n=>n.kind==='cases').length!==2)throw new Error('Interleaved scope sequence did not close structurally');
console.log(JSON.stringify(result.term));
"""
sequence_term=json.loads(subprocess.run(["node","--input-type=module"],input=sequence_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"InterleavedCaseSequence.lean"
    target.write_text("theorem interleaved_cases (P Q U V R T : Prop) (h : P ∨ Q) (j : U ∨ V) (p : P) (f : P → R) (g : P → T) (k : Q → T) (l : U → T) (m : V → T) : T := "+sequence_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Ordinary proof lines interleaved with sequential case scopes elaborate in Lean")

# The same prefix/child-scope composition is needed inside an outer branch.
branch_sequence_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['T','Prop'],
 ['h','P ∨ Q'],['j','U ∨ V'],['f','P → U'],['g','U → T'],['k','V → T'],['m','Q → T']]);
const input='cases h, establish ht : $T$\\n'+
 '  left case hp\\n    establish hu : $U$ | f hp\\n'+
 '    cases j, establish jt : $T$\\n      left case hj\\n        $T$ | g hu\\n      right case hv\\n        $T$ | k hv\\n'+
 '    $T$ | jt\\n  right case hq\\n    $T$ | m hq\\n$T$ | ht';
const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'T'});
if(!result.complete)throw new Error('Nested branch sequence did not close structurally');
console.log(JSON.stringify(result.term));
"""
branch_sequence_term=json.loads(subprocess.run(["node","--input-type=module"],input=branch_sequence_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"BranchSequence.lean"
    target.write_text("theorem branch_sequence (P Q U V T : Prop) (h : P ∨ Q) (j : U ∨ V) (f : P → U) (g : U → T) (k : V → T) (m : Q → T) : T := "+branch_sequence_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("An outer branch with a local prefix and nested case scope elaborates in Lean")

# Lean permits a constructor-bound hypothesis to reuse a parent display name.
# The semantic draft must give that local occurrence a fresh identity and
# resolve the parent spelling again after both branch scopes close.
shadow_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['P','Prop'],['Q','Prop'],['R','Prop'],['h','P ∨ Q'],['hp','Q'],['f','P → R'],['g','Q → R']]);
const input='cases h, establish hR : $R$\\n  left case hp\\n    $R$ | f hp\\n  right case hp\\n    $R$ | g hp\\n$Q$ | hp';
const result=compileNaturalDraft(input,[...facts.keys()],facts,{goal:'Q'});
if(!result.complete||!result.term)throw new Error('Lexical case shadowing did not produce a complete candidate');
console.log(JSON.stringify(result.term));
"""
shadow_term=json.loads(subprocess.run(["node","--input-type=module"],input=shadow_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"ShadowedCase.lean"
    target.write_text("theorem shadowed_case (P Q R : Prop) (h : P ∨ Q) (hp : Q) (f : P → R) (g : Q → R) : Q := "+shadow_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("A shadowed branch hypothesis compiles and the parent object is visible again after closure")

# Negation introduction is intuitionistic: assume P and discharge the remaining
# False goal from an explicit local implication P → False. A mere proof of P
# must not be accepted as a proof of False. Ex-falso remains a separate rule.
logic_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['hnot','P → False']]);
const neg=compileNaturalDraft('假设 hp\\n$False$ | hnot hp',['P','hnot'],facts,{goal:'¬ P'});
const not=compileNaturalDraft('假设 hp\\n$False$ | hnot hp',['P','hnot'],facts,{goal:'Not P'});
const alias=compileNaturalDraft('$¬ P$ | hnot',['hnot'],new Map([['hnot','Not P']]),{goal:'¬ P'});
let rejected=false;
try { compileNaturalDraft('假设 hp\\n$False$ | hp',['P'],new Map(),{goal:'¬ P'}); }
catch(error) { rejected=/Surface type of local premise hp .* differs structurally .* Lean definitional equality has not been checked/.test(error.message); }
if(!rejected)throw new Error('A local proof of P was incorrectly accepted as a proof of False');
const exfalso=compileNaturalDraft('From hFalse, we obtain $Q$',['hFalse'],new Map([['hFalse','False']]),{goal:'Q'});
console.log(JSON.stringify([neg.term,not.term,exfalso.term,alias.term]));
"""
neg_term,not_term,exfalso_term,alias_term=json.loads(subprocess.run(["node","--input-type=module"],input=logic_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"IntuitionisticNegation.lean"
    target.write_text("theorem negation_intro (P : Prop) (hnot : P → False) : ¬ P := "+neg_term+"\n"
        +"theorem not_intro (P : Prop) (hnot : P → False) : Not P := "+not_term+"\n"
        +"theorem exfalso (Q : Prop) (hFalse : False) : Q := "+exfalso_term+"\n"
        +"theorem negation_alias (P : Prop) (hnot : Not P) : ¬ P := "+alias_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Intuitionistic negation introduction and explicit False elimination accepted by Lean")

# Explicit classical reductio is distinct from constructive negation
# introduction and ex-falso, and the generated Lean candidate is compiled.
classical_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const facts=new Map([['h','¬ ¬ P']]);
const result=compileNaturalDraft('classical reductio hnot\\n  contradiction\\n    $False$ | h hnot',['h'],facts,{goal:'P'});
if(!result.complete||result.semanticFidelity!=='not-assessed')throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
classical_term=json.loads(subprocess.run(["node","--input-type=module"],input=classical_script,text=True,cwd=root,check=True,capture_output=True).stdout)
assert "Classical.byContradiction" in classical_term and "h hnot" in classical_term,classical_term
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"ClassicalReductio.lean"
    target.write_text("import Lean\ntheorem double_negation_elimination (P : Prop) (h : ¬ ¬ P) : P := "+classical_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Explicit classical reductio candidate accepted by Lean")

# Also exercise the operation under case-local hypotheses; each branch's
# temporary negation must close before the common result returns to its parent.
case_classical_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const input='cases h, establish result : $P$\\n  left case hp\\n    classical reductio hnot\\n      contradiction\\n        $False$ | hnot hp\\n  right case hq\\n    classical reductio hnot\\n      contradiction\\n        $False$ | hnot hq\\n$P$ | result';
const result=compileNaturalDraft(input,['h'],new Map([['h','P ∨ P']]),{goal:'P'});
if(!result.complete)throw new Error(JSON.stringify(result));
console.log(JSON.stringify(result.term));
"""
case_classical_term=json.loads(subprocess.run(["node","--input-type=module"],input=case_classical_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"CaseLocalClassical.lean"
    target.write_text("import Lean\ntheorem case_local_classical (P : Prop) (h : P ∨ P) : P := "+case_classical_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Classical reductio in both isolated disjunction branches accepted by Lean")

# A conjunction goal opens two identity-isolated child scopes. Local assumptions
# are discharged inside their child, and the same operation composes inside a
# disjunction branch without exporting branch-local names.
subgoal_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const pair=compileNaturalDraft(`split conjunction
  first goal
    $P$ | hp
  second goal
    $Q$ | hq`,['hp','hq'],new Map([['hp','P'],['hq','Q']]),{goal:'P ∧ Q'});
const local=compileNaturalDraft(`假设 hp : $P$
split conjunction
  first goal
    $P$ | hp
  second goal
    $P$ | hp`,[],new Map(),{goal:'P → (P ∧ P)'});
const nested=compileNaturalDraft(`cases h, establish hab : $A ∧ B$
  left case hp
    split conjunction
      first goal
        $A$ | fa hp
      second goal
        $B$ | fb hp
  right case hq
    split conjunction
      first goal
        $A$ | ga hq
      second goal
        $B$ | gb hq
$A ∧ B$ | hab`,['h','fa','fb','ga','gb'],new Map([['h','P ∨ Q'],['fa','P → A'],['fb','P → B'],['ga','Q → A'],['gb','Q → B']]),{goal:'A ∧ B'});
const iff=compileNaturalDraft(`prove equivalence
  forward direction
    assume hp : $P$
    $Q$ | f hp
  reverse direction
    assume hq : $Q$
    $P$ | g hq`,['f','g'],new Map([['f','P → Q'],['g','Q → P']]),{goal:'P ↔ Q'});
const exists=compileNaturalDraft(`construct witness a
  witness property
    $P(a)$ | ha`,['a','ha'],new Map([['a','Nat'],['ha','P a']]),{goal:'∃ x : Nat, P x'});
const nestedExists=compileNaturalDraft(`cases h, establish hex : $∃ x : Nat, P(x)$
  left case hpa
    construct witness a
      witness property
        $P(a)$ | hpa
  right case hq
    construct witness a
      witness property
        $P(a)$ | ha`,['a','ha','h'],new Map([['a','Nat'],['ha','P a'],['h','P a ∨ Q']]),{goal:'∃ x : Nat, P x'});
console.log(JSON.stringify([pair.term,local.term,nested.term,iff.term,exists.term,nestedExists.term]));
"""
pair_term,local_term,nested_pair_term,iff_term,exists_term,nested_exists_term=json.loads(subprocess.run(["node","--input-type=module"],input=subgoal_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"ConjunctionSubgoals.lean"
    target.write_text("theorem conjunction_subgoals (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := "+pair_term+"\n"
        +"theorem conjunction_local_intro (P : Prop) : P → P ∧ P := "+local_term+"\n"
        +"theorem conjunction_inside_cases (A B P Q : Prop) (h : P ∨ Q) (fa : P → A) (fb : P → B) (ga : Q → A) (gb : Q → B) : A ∧ B := "+nested_pair_term+"\n"
        +"theorem iff_subgoals (P Q : Prop) (f : P → Q) (g : Q → P) : P ↔ Q := "+iff_term+"\n"
        +"theorem exists_explicit_witness (P : Nat → Prop) (a : Nat) (ha : P a) : ∃ x : Nat, P x := "+exists_term+"\n"
        +"theorem exists_inside_cases (P : Nat → Prop) (Q : Prop) (a : Nat) (ha : P a) (h : P a ∨ Q) : ∃ x : Nat, P x := "+nested_exists_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Conjunction, equivalence and explicit existential child goals accepted by Lean")

# Restricted element requests preserve the two constructors hidden by Lean's
# bounded-quantifier notation: universal introduction leaves membership as a
# premise, while existential elimination exposes membership together with the
# requested predicate. Both fragments come from the browser's actual parser.
restricted_script = """
import {compileNaturalDraft} from './web/natural-draft.mjs';
const universalFacts=new Map([['A','List Nat'],['hall','∀ x : Nat, x ∈ A → P x']]);
const universal=compileNaturalDraft(`take an arbitrary element x : $Nat$ in A satisfying $P(x)$
assume hx : $x ∈ A$
$P(x)$ | hall x hx`,['A','hall'],universalFacts,{goal:'∀ x ∈ A, P x'});
const existentialFacts=new Map([['A','List Nat'],['h','∃ x ∈ A, P x'],['hq','Q']]);
const existential=compileNaturalDraft(`take an element x : $Nat$ in A satisfying $P(x)$ from h
$Q$ | hq`,['A','h','hq'],existentialFacts,{goal:'Q'});
console.log(JSON.stringify([universal.term,existential.term]));
"""
restricted_universal, restricted_existential = json.loads(subprocess.run(
    ["node", "--input-type=module"], input=restricted_script, text=True,
    cwd=root, check=True, capture_output=True).stdout)
assert "intro x" in restricted_universal and "intro hx" in restricted_universal, restricted_universal
assert "rcases duet_exists_x with ⟨x, h_x⟩" in restricted_existential, restricted_existential
with TemporaryDirectory() as tmp:
    target = Path(tmp) / "RestrictedElements.lean"
    target.write_text(
        "theorem restricted_forall (A : List Nat) (P : Nat → Prop) "
        "(hall : ∀ x : Nat, x ∈ A → P x) : ∀ x ∈ A, P x := "
        + restricted_universal + "\n"
        + "theorem restricted_exists (A : List Nat) (P : Nat → Prop) (Q : Prop) "
        + "(h : ∃ x ∈ A, P x) (hq : Q) : Q := "
        + restricted_existential + "\n", encoding="utf-8")
    subprocess.run(["lean", str(target)], cwd=root, check=True)
print("Generated bounded universal introduction and existential extraction accepted by Lean")

# An aligned set-theory case exercises presentation syntax, bounded context
# introductions and the resulting Lean term. The minimal predicate-set model
# uses Lean's core Membership and Inter classes; no copied Mathlib source is
# needed for this fixture.
real_math_cases=json.loads((root/"tests/fixtures/real-math-cases.json").read_text(encoding="utf-8"))
for real_math_case in real_math_cases:
    case_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const example="""+json.dumps(real_math_case,ensure_ascii=False)+""";
const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
console.log(JSON.stringify(result.term));
"""
    case_term=json.loads(subprocess.run(["node","--input-type=module"],input=case_script,text=True,cwd=root,check=True,capture_output=True).stdout)
    with TemporaryDirectory() as tmp:
        target=Path(tmp)/(real_math_case["id"]+".lean")
        case_source=real_math_case["leanPrelude"]+real_math_case["leanDeclaration"]+case_term+"\n"
        target.write_text(case_source,encoding="utf-8")
        subprocess.run(["lean",str(target)],cwd=root,check=True)
    case_tree=extract(case_source)["tree"]
    focus=next(node for node in walk(case_tree)
               if node.get("reference","").endswith(real_math_case["focusReference"])
               and node.get("term")==real_math_case["expectedElaboratedTerm"])
    assert focus.get("type")==real_math_case["expectedFocusType"],(real_math_case["id"],focus)
    context={binding["name"]:binding for binding in focus["scope"]}
    closure={binding["name"] for binding in focus["scope"] if binding["neededForContext"]}
    assert set(real_math_case["expectedContextClosure"]).issubset(closure),(real_math_case["id"],closure)
    assert real_math_case["focusCandidate"] in case_term,(real_math_case["id"],case_term)
    if real_math_case["id"]=="predicate-intersection-left":
        assert context["hx"]["usedInTerm"] and context["A"]["usedInType"] and context["x"]["usedInType"],context
    else:
        # Lean elaborates the source-level And.intro as constructor notation.
        # Keep that distinction visible instead of demanding textual node identity.
        pair=next((node for node in walk(case_tree)
                   if "hB" in node.get("term","") and "hA" in node.get("term","")
                   and "∧" in node.get("type", "")),None)
        assert pair,case_tree
        # Prefer the explicit constructor when the bounded inspection reaches it;
        # allow opaque only when the expression is actually budget-truncated.
        assert (pair.get("kind")=="apply" and pair.get("reference")=="And.intro") or \
               (pair.get("kind")=="opaque" and pair.get("truncated") is True),pair
    print("Lean-compiled aligned set case:",real_math_case["id"])


# The shared subgoal engine models one bounded inductive constructor: explicit
# induction over a universally quantified Nat target, with a local IH in the
# successor branch and no branch-local object escaping to the parent.
nat_induction_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const constant=compileNaturalDraft(`induction n
  zero case
    $Q$ | hq
  successor case
    $Q$ | ih`,['Q','hq'],new Map([['Q','Prop'],['hq','Q']]),{goal:'∀ n : Nat, Q'});
const dependent=compileNaturalDraft(`对 n 归纳
  基例
    $0 = 0$ | rfl
  归纳步
    $n_step + 1 = n_step + 1$ | rfl`,[],new Map(),{goal:'∀ n : Nat, n = n'});
const step=compileNaturalDraft(`induction n
  zero case
    $P(0)$ | hbase
  successor case
    $P(n_step + 1)$ | hstep n_step ih`,['P','hbase','hstep'],new Map([
  ['P','Nat → Prop'],['hbase','P(0)'],['hstep','∀ k : Nat, P(k) → P(k + 1)']
]),{goal:'∀ n : Nat, P(n)'});
const nested=compileNaturalDraft(`induction n
  zero case
    induction m
      zero case
        $0 = 0$ | rfl
      successor case
        $m_step + 1 = m_step + 1$ | rfl
  successor case
    induction m
      zero case
        $0 = 0$ | rfl
      successor case
        $m_step + 1 = m_step + 1$ | rfl`,[],new Map(),{goal:'∀ n : Nat, ∀ m : Nat, m = m'});
const splitInduction=compileNaturalDraft(`case split h, establish hN : $∀ n : Nat, n = n$
  left case hp
    induction n
      zero case
        $0 = 0$ | rfl
      successor case
        $n_step + 1 = n_step + 1$ | rfl
  right case hq
    induction n
      zero case
        $0 = 0$ | rfl
      successor case
        $n_step + 1 = n_step + 1$ | rfl`,['h'],new Map([['h','P ∨ Q']]),{goal:'∀ n : Nat, n = n'});
for(const result of [constant,dependent,step,nested])if(!result.complete||result.steps.at(-1)?.kind!=='nat-induction')throw new Error(JSON.stringify(result));
if(!splitInduction.complete||splitInduction.rows[0]?.kind!=='cases')throw new Error(JSON.stringify(splitInduction));
if(!constant.rows[0].dependencies.includes('context:1'))throw new Error(JSON.stringify(constant.rows[0]));
if(constant.rows[0].dependencies.some(id=>id.includes('/binding:')))throw new Error('Step-local objects escaped the induction operation');
console.log(JSON.stringify([constant.term,dependent.term,step.term,nested.term,splitInduction.term]));
"""
induction_constant,induction_dependent,induction_step,induction_nested,induction_split=json.loads(subprocess.run(
    ["node","--input-type=module"],input=nat_induction_script,text=True,cwd=root,
    check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"NatInduction.lean"
    target.write_text("import Lean\ntheorem nat_induction_constant (Q : Prop) (hq : Q) : ∀ n : Nat, Q := "
        +induction_constant+"\ntheorem nat_induction_reflexive : ∀ n : Nat, n = n := "
        +induction_dependent+"\ntheorem nat_induction_step (P : Nat → Prop) (hbase : P 0) "
        +"(hstep : ∀ k : Nat, P k → P (k + 1)) : ∀ n : Nat, P n := "
        +induction_step+"\ntheorem nat_induction_nested : ∀ n : Nat, ∀ m : Nat, m = m := "
        +induction_nested+"\ntheorem nat_induction_after_split (P Q : Prop) (h : P ∨ Q) : "
        +"∀ n : Nat, n = n := "+induction_split+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Explicit Nat induction opens isolated base/successor goals and compiles in Lean")

with TemporaryDirectory() as tmp:
    target=Path(tmp)/"IntuitionisticNegation.lean"
    target.write_text("theorem negation_intro (P : Prop) (hnot : P → False) : ¬ P := "+neg_term+"\n"
        +"theorem not_intro (P : Prop) (hnot : P → False) : Not P := "+not_term+"\n"
        +"theorem exfalso (Q : Prop) (hFalse : False) : Q := "+exfalso_term+"\n"
        +"theorem negation_alias (P : Prop) (hnot : Not P) : ¬ P := "+alias_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Intuitionistic negation introduction and explicit False elimination accepted by Lean")

# A conjunction goal opens two identity-isolated child scopes. Local assumptions
# are discharged inside their child, and the same operation composes inside a
# disjunction branch without exporting branch-local names.
subgoal_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const pair=compileNaturalDraft(`split conjunction
  first goal
    $P$ | hp
  second goal
    $Q$ | hq`,['hp','hq'],new Map([['hp','P'],['hq','Q']]),{goal:'P ∧ Q'});
const local=compileNaturalDraft(`假设 hp : $P$
split conjunction
  first goal
    $P$ | hp
  second goal
    $P$ | hp`,[],new Map(),{goal:'P → (P ∧ P)'});
const nested=compileNaturalDraft(`cases h, establish hab : $A ∧ B$
  left case hp
    split conjunction
      first goal
        $A$ | fa hp
      second goal
        $B$ | fb hp
  right case hq
    split conjunction
      first goal
        $A$ | ga hq
      second goal
        $B$ | gb hq
$A ∧ B$ | hab`,['h','fa','fb','ga','gb'],new Map([['h','P ∨ Q'],['fa','P → A'],['fb','P → B'],['ga','Q → A'],['gb','Q → B']]),{goal:'A ∧ B'});
const iff=compileNaturalDraft(`prove equivalence
  forward direction
    assume hp : $P$
    $Q$ | f hp
  reverse direction
    assume hq : $Q$
    $P$ | g hq`,['f','g'],new Map([['f','P → Q'],['g','Q → P']]),{goal:'P ↔ Q'});
const exists=compileNaturalDraft(`construct witness a
  witness property
    $P(a)$ | ha`,['a','ha'],new Map([['a','Nat'],['ha','P a']]),{goal:'∃ x : Nat, P x'});
const nestedExists=compileNaturalDraft(`cases h, establish hex : $∃ x : Nat, P(x)$
  left case hpa
    construct witness a
      witness property
        $P(a)$ | hpa
  right case hq
    construct witness a
      witness property
        $P(a)$ | ha`,['a','ha','h'],new Map([['a','Nat'],['ha','P a'],['h','P a ∨ Q']]),{goal:'∃ x : Nat, P x'});
console.log(JSON.stringify([pair.term,local.term,nested.term,iff.term,exists.term,nestedExists.term]));
"""
pair_term,local_term,nested_pair_term,iff_term,exists_term,nested_exists_term=json.loads(subprocess.run(["node","--input-type=module"],input=subgoal_script,text=True,cwd=root,check=True,capture_output=True).stdout)
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"ConjunctionSubgoals.lean"
    target.write_text("theorem conjunction_subgoals (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := "+pair_term+"\n"
        +"theorem conjunction_local_intro (P : Prop) : P → P ∧ P := "+local_term+"\n"
        +"theorem conjunction_inside_cases (A B P Q : Prop) (h : P ∨ Q) (fa : P → A) (fb : P → B) (ga : Q → A) (gb : Q → B) : A ∧ B := "+nested_pair_term+"\n"
        +"theorem iff_subgoals (P Q : Prop) (f : P → Q) (g : Q → P) : P ↔ Q := "+iff_term+"\n"
        +"theorem exists_explicit_witness (P : Nat → Prop) (a : Nat) (ha : P a) : ∃ x : Nat, P x := "+exists_term+"\n"
        +"theorem exists_inside_cases (P : Nat → Prop) (Q : Prop) (a : Nat) (ha : P a) (h : P a ∨ Q) : ∃ x : Nat, P x := "+nested_exists_term+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True)
print("Conjunction, equivalence and explicit existential child goals accepted by Lean")

# An aligned set-theory case exercises presentation syntax, bounded context
# introductions and the resulting Lean term. The minimal predicate-set model
# uses Lean's core Membership and Inter classes; no copied Mathlib source is
# needed for this fixture.
real_math_cases=json.loads((root/"tests/fixtures/real-math-cases.json").read_text(encoding="utf-8"))
for real_math_case in real_math_cases:
    case_script="""
import {compileNaturalDraft} from './web/natural-draft.mjs';
const example="""+json.dumps(real_math_case,ensure_ascii=False)+""";
const result=compileNaturalDraft(example.naturalDraft,example.scope,new Map(Object.entries(example.context)),{goal:example.goal});
console.log(JSON.stringify(result.term));
"""
    case_term=json.loads(subprocess.run(["node","--input-type=module"],input=case_script,text=True,cwd=root,check=True,capture_output=True).stdout)
    with TemporaryDirectory() as tmp:
        target=Path(tmp)/(real_math_case["id"]+".lean")
        case_source=real_math_case["leanPrelude"]+real_math_case["leanDeclaration"]+case_term+"\n"
        target.write_text(case_source,encoding="utf-8")
        subprocess.run(["lean",str(target)],cwd=root,check=True)
    case_tree=extract(case_source)["tree"]
    focus=next(node for node in walk(case_tree)
               if node.get("reference","").endswith(real_math_case["focusReference"])
               and node.get("term")==real_math_case["expectedElaboratedTerm"])
    assert focus.get("type")==real_math_case["expectedFocusType"],(real_math_case["id"],focus)
    context={binding["name"]:binding for binding in focus["scope"]}
    closure={binding["name"] for binding in focus["scope"] if binding["neededForContext"]}
    assert set(real_math_case["expectedContextClosure"]).issubset(closure),(real_math_case["id"],closure)
    assert real_math_case["focusCandidate"] in case_term,(real_math_case["id"],case_term)
    if real_math_case["id"]=="predicate-intersection-left":
        assert context["hx"]["usedInTerm"] and context["A"]["usedInType"] and context["x"]["usedInType"],context
    else:
        # Lean elaborates the source-level And.intro as constructor notation.
        # Keep that distinction visible instead of demanding textual node identity.
        pair=next((node for node in walk(case_tree)
                   if "hB" in node.get("term","") and "hA" in node.get("term","")
                   and "∧" in node.get("type", "")),None)
        assert pair,case_tree
        # The elaborator may expose And.intro or a genuinely fuel-truncated node.
        assert (pair.get("kind")=="apply" and pair.get("reference")=="And.intro") or \
               (pair.get("kind")=="opaque" and pair.get("truncated") is True),pair
    print("Lean-compiled aligned set case:",real_math_case["id"])
