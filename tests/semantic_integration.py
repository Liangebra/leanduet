import json
"""Actual Lean extraction smoke test; requires the pinned Lean toolchain."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from semantic import extract
source = """theorem composition (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  exact hqr (hpq hp)
"""
r=extract(source)
assert r["schema"]==1 and r["declaration"]=="composition",r
def walk(n):
    yield n
    for c in n["children"]:
        yield from walk(c)
nodes=list(walk(r["tree"]))
assert any(n["kind"]=="assume" for n in nodes),nodes
assert any(n["kind"]=="apply" and "hqr" in n.get("reference","") for n in nodes),nodes
assert any(n["kind"]=="apply" and "hpq" in n.get("reference","") for n in nodes),nodes
print("Actual elaborated proof term extracted:",len(nodes),"nodes")


from semantic import patch
source2 = """theorem patch_example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hq : Q) : P → R := by
  intro hp
  exact hqr (hpq hp)
"""
tree=extract(source2)["tree"]
target=next(n for n in walk(tree) if n["kind"]=="apply" and n.get("reference")=="hpq")
assert target["editable"] and target["path"].startswith("root/"), target
r=patch(source2,target["path"],"hq")
assert r["statementDefEq"] and r["proofShapePreserved"] and r["status"]=="checked",r
assert any(d["name"]=="hq" and d["type"]=="Q" and d["matchesGoal"] for d in target["scope"]), target
assert not any(d["name"]=="hp" and d["matchesGoal"] for d in target["scope"]), target
assert any(a["function"]=="hpq" and a["argument"]=="hp" for a in target["applications"]),target
noop=patch(source2,target["path"],"hpq hp")
assert noop["unchanged"] and noop["source"]==source2,noop
assert "hqr hq" in r["source"],r
for invalid in ["hp", "unknownVariable", "by sorry"]:
    try:
        patch(source2,target["path"],invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("Invalid replacement accepted: "+invalid)
print("Typed replacement, standalone recompilation, statement comparison and rejection passed")

same_type = """theorem same_type (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
target=next(n for n in walk(extract(same_type)["tree"]) if n["kind"]=="hypothesis" and n["term"]=="h1")
r=patch(same_type,target["path"],"h2")
assert r["proofShapePreserved"] and not r["unchanged"],r
assert "h2" in r["source"],r
print("Same-proposition assumptions retain their distinct proof occurrences; no-op preserves source")

source3 = """theorem witness_example : ∃ n : Nat, True := by
  exact ⟨0, True.intro⟩
"""
w=next(n for n in walk(extract(source3)["tree"]) if n["kind"]=="witness")
assert w["type"]=="Nat" and w["editable"],w
r=patch(source3,w["path"],"1")
assert r["proofShapePreserved"] and not r["unchanged"],r

dependent = """theorem dependent_witness : ∃ n : Nat, n = 0 := by
  exact ⟨0, rfl⟩
"""
w=next(n for n in walk(extract(dependent)["tree"]) if n["kind"]=="witness")
try:
    patch(dependent,w["path"],"1")
except ValueError:
    pass
else:
    raise AssertionError("Invalid dependent witness accepted")

quantified = """theorem quantified (P : Nat → Prop) (h : ∀ n : Nat, P n) (a : Nat) : P a := by
  exact h a
"""
q=next(n for n in walk(extract(quantified)["tree"]) if n.get("reference")=="h" and n["kind"]=="apply")
assert any(a["function"]=="h" and a["argument"]=="a" for a in q["applications"]),q
print("Dependent applications and existential witness replacement/rejection passed")

pair_source = """theorem witness_pair : ∃ n : Nat, n = n := by
  exact ⟨0, rfl⟩
"""
pair_node=next(n for n in walk(extract(pair_source)["tree"]) if n.get("reference")=="Exists.intro")
single=next(n for n in pair_node["children"] if n["kind"]=="witness")
try:
    patch(pair_source,single["path"],"1")
except ValueError:
    pass
else:
    raise AssertionError("Stale equality evidence accepted after witness change")
r=patch(pair_source,pair_node["path"],"Exists.intro (1 : Nat) rfl")
assert r["proofShapePreserved"] and r["statementDefEq"] and not r["unchanged"],r
print("Atomic dependent witness/evidence replacement passed")


# Direct syntactic occurrences distinguish hypotheses even when their types coincide.
dep_source = """theorem dependency_example (P : Prop) (h1 h2 : P) : P := by
  exact h1
"""
dep_node=next(n for n in walk(extract(dep_source)["tree"]) if n["kind"]=="hypothesis" and n["term"]=="h1")
scope={d["name"]:d for d in dep_node["scope"]}
assert scope["h1"]["usedInTerm"] and not scope["h2"]["usedInTerm"],scope
assert scope["P"]["usedInType"] and not scope["h1"]["usedInType"],scope
print("Direct expression dependencies preserve distinct local hypotheses")


# A dependent object or function can require an earlier variable without
# mentioning it directly in the selected application or its result type.
closure_source = """theorem context_closure (n : Nat) (f : Fin (n+1) → True) (x : Fin (n+1)) : True := by
  exact f x
"""
closure_node=next(n for n in walk(extract(closure_source)["tree"]) if n.get("reference")=="f")
ctx={d["name"]:d for d in closure_node["scope"]}
assert ctx["f"]["usedInTerm"] and ctx["x"]["usedInTerm"],ctx
assert not ctx["n"]["usedInTerm"] and not ctx["n"]["usedInType"],ctx
assert ctx["n"]["neededForContext"],ctx
assert ctx["n"]["contextIndex"] in ctx["f"]["dependsOn"],ctx
assert ctx["n"]["contextIndex"] in ctx["x"]["dependsOn"],ctx
print("Dependent context closure retained the type of a referenced local object")


# The reading profile projects the same actual proof; it deliberately
# skips the eager alternative-application search.
fast=extract(quantified,reading_only=True)
assert fast["profile"]=="reading",fast
full=extract(quantified)
def without_alternatives(t):
    return {k: ([without_alternatives(c) for c in v] if k=="children" else v)
            for k,v in t.items() if k!="applications"}
assert without_alternatives(fast["tree"])==without_alternatives(full["tree"])
assert all(not n.get("applications") for n in walk(fast["tree"]))
print("Reading profile preserves occurrence tree and skips eager search")


# The trace adapter reads Lean's actual TacticInfo nodes. Goal transitions and
# source ranges are taken from the elaborator, never reconstructed from indentation.
from semantic import trace
trace_source = """import Lean

theorem trace_pair (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- λ: source bytes must map through the imported prelude.
  constructor
  · exact hp
  · exact hq
"""
trace_result = trace(trace_source)
assert trace_result["schema"] == 1 and trace_result["declaration"] == "trace_pair", trace_result

def walk_trace(nodes):
    for node in nodes:
        yield node
        yield from walk_trace(node.get("children", []))

trace_nodes = list(walk_trace(trace_result["tactics"]))
assert trace_nodes, trace_result
for node in trace_nodes:
    span = node["sourceRange"]
    assert 0 <= span["startByte"] < span["endByte"] <= len(trace_source.encode("utf-8")), node
    assert 1 <= span["start"]["line"] <= span["end"]["line"], node
constructor = next(node for node in trace_nodes if node["syntax"].strip().startswith("constructor"))
assert len(constructor["goalsBefore"]) == 1, constructor
# This InfoTree node covers the full constructor block, including both nested
# bullets; its post-state is therefore the completed parent goal.
assert constructor["goalsAfter"] == [], constructor
assert "∧" in constructor["goalsBefore"][0]["target"], constructor
assert {d["name"] for d in constructor["goalsBefore"][0]["localContext"]} >= {"hp", "hq"}, constructor
exact_hp = next(node for node in trace_nodes if node["syntax"].strip() == "exact hp")
assert len(exact_hp["goalsBefore"]) == 1 and exact_hp["goalsAfter"] == [], exact_hp
assert exact_hp["goalsBefore"][0]["target"] == "P", exact_hp
assert "hp" in {d["name"] for d in exact_hp["referencedLocals"]}, exact_hp
assert exact_hp["assignedProofTermCount"] == 1 and exact_hp["assignedProofTermsClosed"], exact_hp
assert exact_hp["sourceRange"]["start"]["line"] == 6, exact_hp
mapped_source = trace_source.encode("utf-8")[exact_hp["sourceRange"]["startByte"]:exact_hp["sourceRange"]["endByte"]].decode("utf-8")
assert mapped_source.strip() == "exact hp", (mapped_source, exact_hp)
exact_hq = next(node for node in trace_nodes if node["syntax"].strip() == "exact hq")
assert exact_hq["goalsBefore"][0]["target"] == "Q", exact_hq
assert "hq" in {d["name"] for d in exact_hq["referencedLocals"]}, exact_hq
assert trace(trace_source) == trace_result, "Same source must produce a deterministic trace."

opaque_source = """theorem opaque_trace (P : Prop) (h : P) : P := by
  assumption
"""
opaque_result = trace(opaque_source)
opaque_tactic = next(node for node in walk_trace(opaque_result["tactics"]) if node["syntax"].strip() == "assumption")
assert opaque_tactic["opaque"] is True, opaque_tactic
assert opaque_tactic["opaqueRange"] == opaque_tactic["sourceRange"], opaque_tactic
assert opaque_tactic["assignedProofTermsClosed"] and "h" in {d["name"] for d in opaque_tactic["referencedLocals"]}, opaque_tactic
print("TRACE_SCHEMA_SAMPLE=" + json.dumps(trace_result, ensure_ascii=False, sort_keys=True))
print("Pinned Lean InfoTree trace captured imported-source byte ranges, nested goals, local context, deterministic output and opaque mappings")
