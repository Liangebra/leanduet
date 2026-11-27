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
