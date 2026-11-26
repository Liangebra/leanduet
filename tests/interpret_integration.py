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
