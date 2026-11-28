"""Actual structural Lean judgment and formula elaboration, independent of pretty printing."""
from pathlib import Path
from tempfile import TemporaryDirectory
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

# Reusing a display name in a nested binder is lexical shadowing, not a
# reference to the outer object. The canonical term should match a fresh-name
# presentation that refers to its innermost binder twice.
shadowed_formula = compile_browser_formula(
    r"\forall n : \mathbb{N}, \forall n : \mathbb{N}, n = n"
)
fresh_shadow_equivalent = compile_browser_formula(
    r"\forall outer : \mathbb{N}, \forall inner : \mathbb{N}, inner = inner"
)
shadowed_scoped = shadowed_formula["scoped"]
shadowed_equality = shadowed_scoped["body"]["body"]
assert shadowed_scoped["body"]["kind"] == "binder", shadowed_scoped
assert shadowed_equality["kind"] == "binary" and shadowed_equality["op"] == "=", shadowed_scoped
assert shadowed_equality["left"] == {"kind": "bound", "index": 0}, shadowed_scoped
assert shadowed_equality["right"] == {"kind": "bound", "index": 0}, shadowed_scoped
assert shadowed_scoped == fresh_shadow_equivalent["scoped"]
assert shadowed_formula["lean"] != fresh_shadow_equivalent["lean"]

def check_browser_formula(candidate, theorem_name, expected_bound_indices=(0, 0, 1, 1)):
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
    # Lean may hygienically rename binder display names in the theorem type.
    # Compare alpha-normalized shape; matchesGoal is Lean's elaborated check.
    assert erase_native_binder_names(judgment["formula"]["term"]) == erase_native_binder_names(judgment["type"]), ir
    native_type = judgment["type"]
    assert native_type[0] == "pi", native_type
    assert native_type[3][0] == "const" and "Nat" in json.dumps(native_type[3][1]), native_type
    inner = native_type[4]
    assert inner[0] == "pi", native_type
    assert inner[3][0] == "const" and "Nat" in json.dumps(inner[3][1]), native_type
    body = inner[4]
    indices = [node[1] for node in expression_nodes(body)
               if len(node) == 2 and node[0] == "bound"]
    assert sorted(indices) == list(expected_bound_indices), native_type
    assert "Eq" in json.dumps(body), native_type
    return native_type

native_type = check_browser_formula(browser_formula, "browser_formula_native_ir")
renamed_native_type = check_browser_formula(renamed_formula, "browser_formula_alpha_native_ir")
assert erase_native_binder_names(native_type) == erase_native_binder_names(renamed_native_type)
shadowed_native_type = check_browser_formula(
    shadowed_formula, "browser_formula_shadowed_native_ir", expected_bound_indices=(0, 0)
)
fresh_shadow_native_type = check_browser_formula(
    fresh_shadow_equivalent, "browser_formula_fresh_shadow_native_ir", expected_bound_indices=(0, 0)
)
assert erase_native_binder_names(shadowed_native_type) == erase_native_binder_names(fresh_shadow_native_type)

print("Browser formula binders retain de Bruijn identity through Lean elaboration and native IR")


# Issue #10: lower the browser's versioned closed Nat/Prop projection into the
# existing typed Lean fragment. A second lowering from the browser's original
# scoped AST checks erasure independently.
scoped_bridge_script = """
import {toScopedSemantics} from './web/math-formula.mjs';
let input = '';
for await (const chunk of process.stdin) input += chunk;
console.log(JSON.stringify(toScopedSemantics(JSON.parse(input))));
"""

def compile_scoped_browser_formula(text):
    result = subprocess.run(
        ["node", "--input-type=module", "-e", scoped_bridge_script],
        input=json.dumps(text),
        text=True,
        capture_output=True,
        cwd=Path(__file__).resolve().parents[1],
        check=True,
    )
    return json.loads(result.stdout)

def fin_literal(index, context_size):
    assert isinstance(index, int) and 0 <= index < context_size, (index, context_size)
    return f"(⟨{index}, by decide⟩ : Fin {context_size})"

def lean_nat_expr(node, context_size):
    kind=node["kind"]
    if kind=="var":
        return (
            "(LeanDuet.ScopedSemantics.NatExpr.var "+fin_literal(node["index"],context_size)
            +" : LeanDuet.ScopedSemantics.NatExpr "+str(context_size)+")"
        )
    if kind=="zero":
        return "(LeanDuet.ScopedSemantics.NatExpr.zero : LeanDuet.ScopedSemantics.NatExpr "+str(context_size)+")"
    if kind=="add":
        left=lean_nat_expr(node["left"],context_size)
        right=lean_nat_expr(node["right"],context_size)
        return (
            "(LeanDuet.ScopedSemantics.NatExpr.add ("+left+") ("+right+")"
            +" : LeanDuet.ScopedSemantics.NatExpr "+str(context_size)+")"
        )
    raise AssertionError("Unexpected projected NatExpr node: "+repr(node))

def lean_formula(node, context_size):
    kind=node["kind"]
    formula_type="LeanDuet.ScopedSemantics.Formula "+str(context_size)
    if kind=="truth":
        return "(LeanDuet.ScopedSemantics.Formula.truth : "+formula_type+")"
    if kind=="falsity":
        return "(LeanDuet.ScopedSemantics.Formula.falsity : "+formula_type+")"
    if kind=="equal":
        left=lean_nat_expr(node["left"],context_size)
        right=lean_nat_expr(node["right"],context_size)
        return (
            "(LeanDuet.ScopedSemantics.Formula.equal ("+left+") ("+right+")"
            +" : "+formula_type+")"
        )
    if kind in ("and","imp"):
        left=lean_formula(node["left"],context_size)
        right=lean_formula(node["right"],context_size)
        constructor="and" if kind=="and" else "imp"
        return (
            "(LeanDuet.ScopedSemantics.Formula."+constructor+" ("+left+") ("+right+")"
            +" : "+formula_type+")"
        )
    if kind=="all":
        body=lean_formula(node["body"],context_size+1)
        return (
            "(LeanDuet.ScopedSemantics.Formula.all ("+body+" : "
            +"LeanDuet.ScopedSemantics.Formula "+str(context_size+1)+")"
            +" : "+formula_type+")"
        )
    raise AssertionError("Unexpected projected Formula node: "+repr(node))

def lean_erased_nat_expr(node, context_size):
    kind=node["kind"]
    if kind=="bound":
        return (
            "(LeanDuet.Scoped.Term.var "+fin_literal(node["index"],context_size)
            +" : LeanDuet.Scoped.Term "+str(context_size)+")"
        )
    if kind=="number" and node["value"]=="0":
        return "(LeanDuet.Scoped.Term.atom \"Nat.zero\" : LeanDuet.Scoped.Term "+str(context_size)+")"
    if kind=="binary" and node["op"]=="+":
        left=lean_erased_nat_expr(node["left"],context_size)
        right=lean_erased_nat_expr(node["right"],context_size)
        return (
            "(LeanDuet.Scoped.Term.binary \"Nat.add\" ("+left+") ("+right+")"
            +" : LeanDuet.Scoped.Term "+str(context_size)+")"
        )
    raise AssertionError("Unexpected browser Nat expression: "+repr(node))

def lean_erased_formula(node, context_size):
    kind=node["kind"]
    term_type="LeanDuet.Scoped.Term "+str(context_size)
    if kind=="free" and node["name"] in ("True","False"):
        return "(LeanDuet.Scoped.Term.atom \""+node["name"]+"\" : "+term_type+")"
    if kind=="binder" and node["op"]=="∀" and node["domain"]=={"kind":"free","name":"Nat"}:
        body=lean_erased_formula(node["body"],context_size+1)
        return (
            "(LeanDuet.Scoped.Term.bind \"∀ Nat\""
            +" (LeanDuet.Scoped.Term.atom \"Nat\" : "+term_type+")"
            +" ("+body+" : LeanDuet.Scoped.Term "+str(context_size+1)+")"
            +" : "+term_type+")"
        )
    if kind=="binary":
        constructors={"=":"Eq","∧":"And","→":"Imp"}
        assert node["op"] in constructors,node
        if node["op"]=="=":
            left=lean_erased_nat_expr(node["left"],context_size)
            right=lean_erased_nat_expr(node["right"],context_size)
        else:
            left=lean_erased_formula(node["left"],context_size)
            right=lean_erased_formula(node["right"],context_size)
        return (
            "(LeanDuet.Scoped.Term.binary \""+constructors[node["op"]]+"\""
            +" ("+left+") ("+right+") : "+term_type+")"
        )
    raise AssertionError("Unexpected browser formula node: "+repr(node))

bridge_inputs = {
    "nested": r"\forall n : \mathbb{N}, \forall m : \mathbb{N}, n + m = n + m",
    "alpha": r"\forall i : \mathbb{N}, \forall j : \mathbb{N}, i + j = i + j",
    "shadow": r"\forall n : \mathbb{N}, \forall n : \mathbb{N}, n = n",
    "shadow_fresh": r"\forall outer : \mathbb{N}, \forall inner : \mathbb{N}, inner = inner",
    "connectives": r"\forall n : \mathbb{N}, n = 0 \to (n + 0 = n \land n = n)",
    "truth": r"\top",
    "falsity": r"\bot",
}
bridge = {}
for name, formula_text in bridge_inputs.items():
    candidate=compile_browser_formula(formula_text)
    projected=compile_scoped_browser_formula(formula_text)
    assert projected["schema"]=="leanduet.scoped-semantics.formula",projected
    assert projected["version"]==1 and projected["contextSize"]==0,projected
    bridge[name]={"candidate":candidate,"projected":projected}
assert bridge["nested"]["projected"]["formula"]==bridge["alpha"]["projected"]["formula"]
assert bridge["shadow"]["projected"]["formula"]==bridge["shadow_fresh"]["projected"]["formula"]

lean_checks=[]
for name, item in bridge.items():
    core=lean_formula(item["projected"]["formula"],0)
    erased=lean_erased_formula(item["candidate"]["scoped"],0)
    lean_checks.append(
        "example : LeanDuet.ScopedSemantics.eraseFormula ("+core
        +" : LeanDuet.ScopedSemantics.Formula 0) = ("+erased
        +" : LeanDuet.Scoped.Term 0) := by rfl"
    )
    lean_checks.append(
        "example : LeanDuet.ScopedSemantics.denote ("+core
        +" : LeanDuet.ScopedSemantics.Formula 0) (fun i => Fin.elim0 i) ↔ (("
        +item["candidate"]["lean"]+" : Prop)) := by rfl"
    )
for left,right in (("nested","alpha"),("shadow","shadow_fresh")):
    left_core=lean_formula(bridge[left]["projected"]["formula"],0)
    right_core=lean_formula(bridge[right]["projected"]["formula"],0)
    lean_checks.append(
        "example : ("+left_core+" : LeanDuet.ScopedSemantics.Formula 0) = ("
        +right_core+" : LeanDuet.ScopedSemantics.Formula 0) := by rfl"
    )
root=Path(__file__).resolve().parents[1]
scoped_source=(root/"lean"/"Scoped.lean").read_text(encoding="utf-8")
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"BrowserScopedSemanticsBridge.lean"
    target.write_text(scoped_source+"\n\n"+"\n".join(lean_checks)+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True,capture_output=True,text=True)
print("Browser AST projection agrees with ScopedSemantics syntax, erasure, and denotation on the tested fragment")


# Explicit local contexts are the next projection boundary: the JSON context
# keeps stable object identity separate from its display name, while Lean checks
# that de Bruijn slots denote the corresponding actual Nat parameters.
context_bridge_script = """
import {toScopedSemanticsInContext} from './web/math-formula.mjs';
let input = '';
for await (const chunk of process.stdin) input += chunk;
const payload = JSON.parse(input);
console.log(JSON.stringify(toScopedSemanticsInContext(payload.text,{context:payload.context})));
"""

def compile_context_scoped_formula(text, context):
    result = subprocess.run(
        ["node", "--input-type=module", "-e", context_bridge_script],
        input=json.dumps({"text":text,"context":context}),
        text=True,
        capture_output=True,
        cwd=Path(__file__).resolve().parents[1],
        check=True,
    )
    return json.loads(result.stdout)

local_context = [
    {"id":"object-x","name":"x","type":"Nat"},
    {"id":"object-y","name":"y","type":"Nat"},
]
context_formula_text = "x + y = y + x"
context_projection = compile_context_scoped_formula(context_formula_text,local_context)
assert context_projection["schema"]=="leanduet.scoped-semantics.formula-context",context_projection
assert context_projection["version"]==1 and context_projection["contextSize"]==2,context_projection
assert context_projection["context"]==local_context,context_projection
assert context_projection["formula"]=={
    "kind":"equal",
    "left":{"kind":"add","left":{"kind":"var","index":1},"right":{"kind":"var","index":0}},
    "right":{"kind":"add","left":{"kind":"var","index":0},"right":{"kind":"var","index":1}},
},context_projection
context_candidate=compile_browser_formula(context_formula_text)
context_core=lean_formula(context_projection["formula"],2)
context_environment="(fun i : Fin 2 => Fin.cases y (fun _ => x) i)"
context_lean_checks=[
    "example (x y : Nat) : LeanDuet.ScopedSemantics.denote ("+context_core
    +" : LeanDuet.ScopedSemantics.Formula 2) "+context_environment
    +" ↔ ("+context_candidate["lean"]+" : Prop) := by rfl"
]

shadow_formula_text="∀ x : Nat, x + y = y + x"
shadow_projection=compile_context_scoped_formula(shadow_formula_text,local_context)
shadow_candidate=compile_browser_formula(shadow_formula_text)
shadow_core=lean_formula(shadow_projection["formula"],2)
context_lean_checks.append(
    "example (x y : Nat) : LeanDuet.ScopedSemantics.denote ("+shadow_core
    +" : LeanDuet.ScopedSemantics.Formula 2) "+context_environment
    +" ↔ ("+shadow_candidate["lean"]+" : Prop) := by rfl"
)

with TemporaryDirectory() as tmp:
    target=Path(tmp)/"BrowserScopedContextBridge.lean"
    target.write_text(scoped_source+"\n\n"+"\n".join(context_lean_checks)+"\n",encoding="utf-8")
    subprocess.run(["lean",str(target)],cwd=root,check=True,capture_output=True,text=True)
print("Explicit Nat context identities project to the expected Fin slots and preserve Lean denotation")


# Test the serialized context projection against actual capture-avoiding
# substitution, not only against its pointwise interpretation.
substitution_source_text="x + y = y + x"
substitution_source_context=[
    {"id":"object-x","name":"x","type":"Nat"},
    {"id":"object-y","name":"y","type":"Nat"},
]
substitution_source=compile_context_scoped_formula(
    substitution_source_text,substitution_source_context)
substitution_target=compile_context_scoped_formula(
    "0 + z = z + 0",[{"id":"object-z","name":"z","type":"Nat"}])
substitution_source_core=lean_formula(substitution_source["formula"],2)
substitution_target_core=lean_formula(substitution_target["formula"],1)
xy_to_z=(
    "(fun i : Fin 2 => Fin.cases "
    "(LeanDuet.ScopedSemantics.NatExpr.var (⟨0, by decide⟩ : Fin 1) "
    ": LeanDuet.ScopedSemantics.NatExpr 1) "
    "(fun _ => (LeanDuet.ScopedSemantics.NatExpr.zero "
    ": LeanDuet.ScopedSemantics.NatExpr 1)) i)"
)
substitution_lean_checks=[
    "example : LeanDuet.ScopedSemantics.substFormula "+xy_to_z+" ("
    +substitution_source_core+" : LeanDuet.ScopedSemantics.Formula 2) = ("
    +substitution_target_core+" : LeanDuet.ScopedSemantics.Formula 1) := by rfl",
    "example (ρ : LeanDuet.ScopedSemantics.Env 1) : "
    "LeanDuet.ScopedSemantics.denote "
    "(LeanDuet.ScopedSemantics.substFormula "+xy_to_z+" ("
    +substitution_source_core+" : LeanDuet.ScopedSemantics.Formula 2)) ρ = "
    "LeanDuet.ScopedSemantics.denote ("+substitution_source_core
    +" : LeanDuet.ScopedSemantics.Formula 2) "
    "(fun i => LeanDuet.ScopedSemantics.denoteNat ("+xy_to_z
    +" i) ρ) := by exact LeanDuet.ScopedSemantics.denote_subst _ _ _",
]

capture_source=compile_context_scoped_formula(
    "∀ z : Nat, x + z = z + x",
    [{"id":"object-x","name":"x","type":"Nat"}])
capture_target=compile_context_scoped_formula(
    "∀ z : Nat, 0 + z = z + 0",[])
capture_source_core=lean_formula(capture_source["formula"],1)
capture_target_core=lean_formula(capture_target["formula"],0)
x_to_zero=(
    "(fun _ : Fin 1 => (LeanDuet.ScopedSemantics.NatExpr.zero "
    ": LeanDuet.ScopedSemantics.NatExpr 0))"
)
substitution_lean_checks.extend([
    "example : LeanDuet.ScopedSemantics.substFormula "+x_to_zero+" ("
    +capture_source_core+" : LeanDuet.ScopedSemantics.Formula 1) = ("
    +capture_target_core+" : LeanDuet.ScopedSemantics.Formula 0) := by rfl",
    "example (ρ : LeanDuet.ScopedSemantics.Env 0) : "
    "LeanDuet.ScopedSemantics.denote "
    "(LeanDuet.ScopedSemantics.substFormula "+x_to_zero+" ("
    +capture_source_core+" : LeanDuet.ScopedSemantics.Formula 1)) ρ = "
    "LeanDuet.ScopedSemantics.denote ("+capture_source_core
    +" : LeanDuet.ScopedSemantics.Formula 1) "
    "(fun i => LeanDuet.ScopedSemantics.denoteNat ("+x_to_zero
    +" i) ρ) := by exact LeanDuet.ScopedSemantics.denote_subst _ _ _",
])
with TemporaryDirectory() as tmp:
    target=Path(tmp)/"BrowserScopedContextSubstitution.lean"
    target.write_text(
        scoped_source+"\n\n"+"\n".join(substitution_lean_checks)+"\n",
        encoding="utf-8",
    )
    subprocess.run(["lean",str(target)],cwd=root,check=True,capture_output=True,text=True)
print("Versioned browser context projections commute with two checked Nat substitutions, including a binder shift")
