"""Actual structural Lean judgment and formula elaboration, independent of pretty printing."""
from pathlib import Path
import json, subprocess, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract,inspect_ir

def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)

def validate(ir):
    assert ir["judgment"]["roundTrip"]=={"checked":True,"shapePreserved":True,"encodingPreserved":True,"typeDefEq":True,"freshContextChecked":True,"mode":"same-environment-fresh-context"},ir
    script="import {validateJudgment} from './web/semantic-ir.mjs'; import fs from 'node:fs'; validateJudgment(JSON.parse(fs.readFileSync(0,'utf8')));"
    subprocess.run(["node","--input-type=module","-e",script],input=json.dumps(ir),text=True,check=True,cwd=Path(__file__).resolve().parents[1])

source="""theorem ir_identity (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
node=next(n for n in walk(extract(source)["tree"]) if n.get("term")=="h1" and n["kind"]=="hypothesis")
ir=inspect_ir(source,node["path"],"P")
validate(ir)
j=ir["judgment"]
ctx={d["display"]:d for d in j["context"]}
assert j["term"]==["local",ctx["h1"]["slot"]],ir
assert j["type"]==["local",ctx["P"]["slot"]],ir
assert j["formula"]["term"]==j["type"] and j["formula"]["matchesGoal"],ir
assert ctx["h1"]["slot"]!=ctx["h2"]["slot"],ir
assert inspect_ir(source,node["path"],"True")["judgment"]["formula"]["matchesGoal"] is False
root=inspect_ir(source,"root")
validate(root)
assert root["judgment"]["term"][0]=="lambda"
print("Kernel judgment retains local identity, bound variables and typed formula alignment")

source2="""theorem ir_universe (A : Type u) (x : A) : x = x := by
  rfl
"""
root=inspect_ir(source2,"root")
validate(root)
assert root["universes"],root
assert root["judgment"]["term"][0]=="lambda",root
print("Universe-polymorphic read-only IR preserves level parameters")

# Dependent binder, local let, constant universes, literals and applications.
source3="""theorem ir_dependent (n : Nat) (x : Fin (n+1)) : ∃ y : Fin (n+1), y = x := by
  let y := x
  exact ⟨y, rfl⟩
"""
validate(inspect_ir(source3,"root"))
tree=extract(source3)["tree"]
for node in walk(tree):
    if node["kind"]=="witness":
        validate(inspect_ir(source3,node["path"]))
        break
else:
    raise AssertionError("Expected existential witness")
print("Dependent expressions and selected witness survive structural decoding")


from semantic import abstract_preview
source4="""theorem ir_abstract (n : Nat) (f : Fin (n+1) → True) (x : Fin (n+1)) (irrelevant : Nat) : True := by
  exact f x
"""
target=next(n for n in walk(extract(source4)["tree"]) if n.get("reference")=="f")
a=abstract_preview(source4,target["path"])
assert a["closedChecked"] and a["reopenedShape"],a
assert [p["name"] for p in a["parameters"]]==["n","f","x"],a
assert a["standaloneChecked"] and a["exportShapePreserved"] and a["source"],a
assert "theorem LeanDuetExtractedLemma" in a["source"] and "irrelevant" not in a["source"],a
print("Dependency-closed abstraction compiles independently and preserves the proof occurrence")


# Same-type premises remain distinct during abstraction, not just serialization.
a=abstract_preview(source,next(n["path"] for n in walk(extract(source)["tree"]) if n.get("term")=="h1" and n["kind"]=="hypothesis"))
assert [p["name"] for p in a["parameters"]]==["P","h1"],a
assert a["standaloneChecked"] and a["exportShapePreserved"],a
# Universe-polymorphic abstraction is internally checked but not presented as standalone source.
u=abstract_preview(source2,"root")
assert u["closedChecked"] and u["reopenedShape"] and u["universes"],u
assert u["source"] is None and not u["standaloneChecked"],u
print("Abstraction preserves distinct premises and reports the polymorphic export limit")


from semantic import factor_preview
source5="""theorem ir_factor (P Q R : Prop) (f : P → Q) (g : Q → R) (p : P) : R := by
  exact g (f p)
"""
inner=next(n for n in walk(extract(source5)["tree"]) if n.get("reference")=="f")
r=factor_preview(source5,inner["path"])
assert r["standaloneChecked"] and r["statementDefEq"] and r["proofComplementPreserved"] and r["lemmaShapePreserved"],r
assert "theorem LeanDuetExtractedLemma" in r["source"] and "theorem ir_factor" in r["source"],r
assert "g (LeanDuetExtractedLemma" in r["source"],r
print("Factoring a nested inference produces a standalone checked two-theorem document")


# Issue #10: compare the browser's canonical binder view with Lean's native IR
# on a small typed fragment. The browser formula is the source of the Lean
# statement below; Lean elaboration and the native round-trip checker remain
# the authority for typing.
formula_script = """
import {compileFormula} from './web/math-formula.mjs';
let input = '';
for await (const chunk of process.stdin) input += chunk;
console.log(JSON.stringify(compileFormula(JSON.parse(input))));
"""

def compile_browser_formula(text):
    result = subprocess.run(
        ["node", "--input-type=module", "-e", formula_script],
        input=json.dumps(text),
        text=True,
        capture_output=True,
        cwd=Path(__file__).resolve().parents[1],
        check=True,
    )
    return json.loads(result.stdout)

def expression_nodes(expr):
    if isinstance(expr, list):
        yield expr
        for child in expr:
            if isinstance(child, list):
                yield from expression_nodes(child)

def erase_native_binder_names(expr):
    # Expr binder names are display hints; bound indices carry identity.
    if not isinstance(expr, list):
        return expr
    if len(expr) == 5 and expr[0] in ("lambda", "pi"):
        return [expr[0], expr[2], erase_native_binder_names(expr[3]),
                erase_native_binder_names(expr[4])]
    return [erase_native_binder_names(child) for child in expr]

formula_text = r"\forall n : \mathbb{N}, \forall m : \mathbb{N}, n + m = n + m"
browser_formula = compile_browser_formula(formula_text)
scoped = browser_formula["scoped"]
assert scoped["kind"] == "binder" and scoped["op"] == "∀", scoped
outer_body = scoped["body"]
assert outer_body["kind"] == "binder" and outer_body["op"] == "∀", scoped
equality = outer_body["body"]
assert equality["kind"] == "binary" and equality["op"] == "=", scoped
assert equality["left"]["kind"] == "binary" and equality["left"]["op"] == "+", scoped
assert equality["left"] == equality["right"], scoped
assert equality["left"]["left"] == {"kind": "bound", "index": 1}, scoped
assert equality["left"]["right"] == {"kind": "bound", "index": 0}, scoped

# Renaming binders changes their presentation but not either scoped syntax
# or the native Lean expression after binder display names are erased.
renamed_formula = compile_browser_formula(
    r"\forall i : \mathbb{N}, \forall j : \mathbb{N}, i + j = i + j"
)
assert renamed_formula["scoped"] == scoped
assert renamed_formula["lean"] != browser_formula["lean"]

def check_browser_formula(candidate, theorem_name):
    source = (
        f"theorem {theorem_name} : {candidate['lean']} := by\n"
        "  intro _ _\n"
        "  rfl\n"
    )
    # Extracting and inspecting this declaration uses Lean's real elaborator.
    extract(source)
    ir = inspect_ir(source, "root", candidate["lean"])
    validate(ir)
    judgment = ir["judgment"]
    assert judgment["formula"]["matchesGoal"], ir
    assert judgment["formula"]["term"] == judgment["type"], ir
    native_type = judgment["type"]
    assert native_type[0] == "pi", native_type
    assert native_type[3][0] == "const" and "Nat" in json.dumps(native_type[3][1]), native_type
    inner = native_type[4]
    assert inner[0] == "pi", native_type
    assert inner[3][0] == "const" and "Nat" in json.dumps(inner[3][1]), native_type
    body = inner[4]
    indices = [node[1] for node in expression_nodes(body)
               if len(node) == 2 and node[0] == "bound"]
    assert sorted(indices) == [0, 0, 1, 1], native_type
    assert "Eq" in json.dumps(body), native_type
    return native_type

native_type = check_browser_formula(browser_formula, "browser_formula_native_ir")
renamed_native_type = check_browser_formula(renamed_formula, "browser_formula_alpha_native_ir")
assert erase_native_binder_names(native_type) == erase_native_binder_names(renamed_native_type)

print("Browser formula binders retain de Bruijn identity through Lean elaboration and native IR")
