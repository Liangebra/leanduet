"""Opt-in local semantic tools. Execute trusted Lean sources only."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
NAME = re.compile(r"(?m)^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\s")
MAX_OUTPUT = 512 * 1024

def _name(source):
    names = NAME.findall(source)
    if len(names) != 1:
        raise ValueError("Semantic extraction currently requires one ASCII-named theorem or lemma.")
    return names[0]

def _run_lean(text, project=None, marker=None, trace=False):
    command = ["lake", "env", "lean"] if project else ["lean"]
    if not shutil.which(command[0]):
        raise ValueError("Lean toolchain not available.")
    with tempfile.TemporaryDirectory(prefix="leanduet-structure-") as directory:
        path = Path(directory) / "Inspect.lean"
        path.write_text(text, encoding="utf-8")
        r = subprocess.run(command + [str(path)], cwd=project or ROOT, capture_output=True,
                           text=True, encoding="utf-8", errors="replace", timeout=45)
    out = r.stdout + r.stderr
    if r.returncode or re.search(r"\bsorry\b", out):
        raise ValueError("Lean semantic check failed:\n" + (out if len(out)<=8000 else out[:4000]+"\n…\n"+out[-4000:]))
    if marker:
        if marker not in out:
            raise ValueError("Lean did not confirm the required check.")
        return out
    for line in out.splitlines():
        if "LEANDUET_JSON:" in line:
            raw = line.split("LEANDUET_JSON:", 1)[1]
            if len(raw.encode()) > MAX_OUTPUT:
                raise ValueError("Proof tree exceeds the current inspection limit.")
            result = json.loads(raw)
            if trace:
                result['bindings'] = [json.loads(line.split('LEANDUET_BINDING:',1)[1])
                                      for line in out.splitlines() if 'LEANDUET_BINDING:' in line]
            return result
    raise ValueError("No semantic result was produced.")

def _adapter():
    return ((ROOT / "lean" / "Extract.lean").read_text(encoding="utf-8") + "\n" +
            (ROOT / "lean" / "InfoTreeTrace.lean").read_text(encoding="utf-8"))

def extract(source, project=None, *, reading_only=False):
    name = _name(source)
    if re.search(r"\b(?:sorry|admit|sorryAx)\b", source):
        raise ValueError("Incomplete proofs cannot be inspected as verified derivations.")
    return _run_lean("import Lean\n" + source.rstrip() + "\n\n" + _adapter() +
                     ("\n#duet_extract_fast " if reading_only else "\n#duet_extract ") + name + "\n", project)



def trace(source, project=None):
    """Capture tactic ranges and goal/context snapshots from Lean's InfoTree.

    The initial adapter accepts one declaration preceded only by imports. It
    never treats indentation as proof dependency information.
    """
    name = _name(source)
    match = NAME.search(source)
    prelude = source[:match.start()]
    for line in prelude.splitlines():
        if line.strip() and not line.lstrip().startswith("import "):
            raise ValueError("InfoTree tracing accepts only imports before the declaration.")
    declaration = source[match.start():].strip()
    if re.search(r"\\b(?:sorry|admit|sorryAx)\\b", declaration):
        raise ValueError("Incomplete proofs cannot be traced as verified derivations.")
    adapter = _adapter()
    prefix = "import Lean\\n" + prelude + adapter + "\\n#duet_trace\\n"
    output = _run_lean(prefix + declaration + "\\n", project, "LEANDUET_TRACE_JSON:")
    marker = "LEANDUET_TRACE_JSON:"
    encoded = [line.split(marker, 1)[1] for line in output.splitlines() if marker in line]
    if len(encoded) != 1:
        raise ValueError("Lean did not produce exactly one InfoTree trace.")
    if len(encoded[0].encode("utf-8")) > MAX_OUTPUT:
        raise ValueError("InfoTree trace exceeds the current inspection limit.")
    result = json.loads(encoded[0])
    if result.get("schema") != 1:
        raise ValueError("Unsupported InfoTree trace schema.")
    byte_delta = len(prefix.encode("utf-8")) - len(prelude.encode("utf-8"))
    line_delta = prefix.count("\\n") - prelude.count("\\n")
    for tactic in result.get("tactics", []):
        source_range = tactic.get("sourceRange")
        if source_range is None:
            continue
        source_range["startByte"] -= byte_delta
        source_range["endByte"] -= byte_delta
        source_range["start"]["line"] -= line_delta
        source_range["end"]["line"] -= line_delta
        if source_range["startByte"] < 0 or source_range["endByte"] > len(source.encode("utf-8")):
            raise ValueError("InfoTree source range lies outside the supplied declaration.")
    result["declaration"] = name
    result["sourceEncoding"] = "UTF-8"
    result["rangeConvention"] = "half-open UTF-8 byte offsets; 1-based lines; 0-based Unicode-scalar columns"
    return result

def _safe_proof(source):
    if re.search(r"\b(?:sorry|admit|sorryAx)\b", source):
        raise ValueError("Incomplete proofs cannot be used in a typed replacement.")
    return source

def _candidate(name, type_text, term_text, prelude):
    def indent(s):
        return "\n".join("    " + line if line.strip() else "" for line in s.splitlines())
    return (prelude + "theorem " + name + " :\n" + indent(type_text) +
            " := by\n  exact (\n" + indent(term_text) + "\n  )\n")

def patch(source, path, replacement, project=None):
    """Check a replacement preview, never mutate the original source."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path, str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}", path):
        raise ValueError("Invalid proof node path.")
    if not isinstance(replacement, str) or not replacement.strip() or len(replacement) > 16000:
        raise ValueError("Replacement must be a nonempty Lean term of at most 16000 characters.")
    _safe_proof(replacement)
    prelude = source[:NAME.search(source).start()]
    if any(line.strip() and not re.fullmatch(r"import\s+\S.*", line) for line in prelude.splitlines()):
        raise ValueError("Typed export currently supports only imports before the theorem.")
    adapter = _adapter()
    args = " ".join(json.dumps(x,ensure_ascii=False) for x in (path,replacement))
    result = _run_lean("import Lean\n" + source.rstrip() + "\n\n" + adapter +
                       "\n#duet_patch " + name + " " + args + "\n", project)
    unchanged = result.get("unchanged") is True
    candidate = source if unchanged else _safe_proof(_candidate(name, result["type"], result["term"], prelude))
    _run_lean(candidate + '\n#eval "LEANDUET_EXPORT_OK"\n', project, "LEANDUET_EXPORT_OK")
    if unchanged:
        return {"source":source, "path":path, "localType":result["localType"],
                "oldTerm":result["oldTerm"], "status":"checked", "statementDefEq":True,
                "proofShapePreserved":True, "surfaceHeaderChanged":False, "unchanged":True}
    other = "LeanDuetReplacementPreview"
    if name == other or re.search(r"\b" + other + r"\b", source):
        raise ValueError("Reserved preview declaration name.")
    renamed = _candidate(other, result["type"], result["term"], "")
    _run_lean("import Lean\n" + source.rstrip() + "\n\n" + renamed + "\n" + adapter +
              "\n#duet_compare " + name + " " + other + " " + args + "\n", project, "LEANDUET_TYPE_AND_SHAPE_MATCH")
    return {"source":candidate, "path":path, "localType":result["localType"],
            "oldTerm":result["oldTerm"], "status":"checked",
            "statementDefEq":True, "proofShapePreserved":True, "surfaceHeaderChanged":True, "unchanged":False}


_SIMPLE = r"[A-Za-z_][A-Za-z0-9_']{0,63}"
_RULE = r"[A-Za-z_][A-Za-z0-9_'.]{0,159}"

def _ordered_application(app):
    """Restricted named applications with bounded parenthesized arguments."""
    if not isinstance(app, str) or len(app) > 2000:
        return False
    if app == "?":
        return True
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[()]|[ \t]+", app)
    if "".join(tokens) != app:
        return False
    tokens = [t for t in tokens if not t.isspace()]
    forbidden = {"by", "fun", "match", "let", "have", "show", "do", "if", "then", "else", "where", "sorry", "admit", "sorryAx"}
    if len(tokens) > 80 or any(t in forbidden for t in tokens):
        return False
    pos = 0
    def parse(depth):
        nonlocal pos
        if depth > 8 or pos >= len(tokens) or not re.fullmatch(_RULE, tokens[pos]):
            return False
        pos += 1
        argc = 0
        while pos < len(tokens) and tokens[pos] != ")":
            argc += 1
            if argc > 8:
                return False
            if tokens[pos] == "(":
                pos += 1
                if not parse(depth + 1) or pos >= len(tokens) or tokens[pos] != ")":
                    return False
                pos += 1
            elif re.fullmatch(_SIMPLE, tokens[pos]):
                pos += 1
            else:
                return False
        return True
    return parse(0) and pos == len(tokens)

def infer_chain(source, path, steps, project=None):
    """Elaborate an ordered chain at the selected occurrence; never edit source."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path,str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}",path):
        raise ValueError("Invalid proof node path.")
    def annotation(value, label, *, optional=False):
        if optional and value is None:
            return
        if (not isinstance(value,str) or not value.strip() or len(value)>2000 or
            re.search(r"[\r\n;{}]|/-|--|:=|\b(?:by|sorry|admit|sorryAx)\b",value)):
            raise ValueError("Expected "+label+".")

    emitted_steps=[0]
    def emit_sequence(sequence, inherited, depth=1, trace_scope=True, case_depth=0):
        if not isinstance(sequence,list) or not 1<=len(sequence)<=16 or depth>20:
            raise ValueError("Each proof scope needs 1–16 steps and nesting is bounded.")
        known=set(inherited)
        lines_out=[]
        trace_out=[]
        introduced=[]
        pad="  "*depth
        def add(line):
            lines_out.append(pad+line)
            trace_out.append(pad+line)
        for i,step in enumerate(sequence):
            emitted_steps[0]+=1
            if emitted_steps[0]>128:
                raise ValueError("The nested proof exceeds the 128-step elaboration budget.")
            if not isinstance(step,dict):
                raise ValueError("Expected a structured proof step.")
            kind=step.get("kind")
            last=i==len(sequence)-1
            if kind=="conclude" and last:
                app=step.get("application")
                if not _ordered_application(app):
                    raise ValueError("Expected an ordered application of a named rule.")
                ty=step.get("type")
                annotation(ty,"a single conclusion proposition",optional=True)
                if ty is not None:
                    add("show "+ty)
                add("exact?" if app=="?" else "exact "+app)
                continue
            if last:
                raise ValueError("The chain must conclude exactly once, at its last step.")
            if kind=="cases":
                if case_depth>=8:
                    raise ValueError("Nested disjunction scope is limited to eight levels.")
                h,source,ty=step.get("name"),step.get("source"),step.get("type")
                if not isinstance(h,str) or not re.fullmatch(_SIMPLE,h) or h in known:
                    raise ValueError("Invalid or repeated case result name.")
                if not isinstance(source,str) or not re.fullmatch(_SIMPLE,source):
                    raise ValueError("A case split must cite a simple local premise name.")
                annotation(ty,"a single case result proposition")
                branches=step.get("branches")
                if not isinstance(branches,list) or len(branches)!=2 or [b.get("constructor") for b in branches if isinstance(b,dict)]!=["inl","inr"]:
                    raise ValueError("A disjunction split needs one inl and one inr branch.")
                branch_lines=[pad+"have "+h+" : "+ty+" := by",pad+"  cases "+source+" with"]
                branch_trace=list(branch_lines)
                for branch in branches:
                    binder,branch_type=branch.get("name"),branch.get("type")
                    if not isinstance(binder,str) or not re.fullmatch(_SIMPLE,binder) or binder in known:
                        raise ValueError("Invalid or repeated branch-local name.")
                    annotation(branch_type,"a single branch assumption type")
                    if branch.get("goal")!=ty:
                        raise ValueError("Both case branches must prove the declared common result.")
                    constructor=branch["constructor"]
                    arm_pad=pad+"  "
                    branch_lines.append(arm_pad+"| "+constructor+" "+binder+" =>")
                    branch_trace.append(arm_pad+"| "+constructor+" "+binder+" =>")
                    change=arm_pad+"  change "+branch_type+" at "+binder
                    branch_lines.append(change)
                    branch_trace.append(change)
                    body,body_trace,_=emit_sequence(branch.get("steps"),known|{binder},depth+2,False,case_depth+1)
                    branch_lines.extend(body)
                    branch_trace.extend(body_trace)
                lines_out.extend(branch_lines)
                trace_out.extend(branch_trace)
                known.add(h)
                introduced.append(h)
                if trace_scope:
                    trace_out.append(pad+"duet_trace "+h)
                continue
            if kind=="local-lemma":
                h,ty=step.get("name"),step.get("type")
                if not isinstance(h,str) or not re.fullmatch(_SIMPLE,h) or h in known:
                    raise ValueError("Invalid or repeated local lemma name.")
                annotation(ty,"a local lemma proposition")
                subgoals=step.get("subgoals")
                if (not isinstance(subgoals,list) or len(subgoals)!=1 or
                    not isinstance(subgoals[0],dict) or subgoals[0].get("id")!="proof" or
                    subgoals[0].get("goal")!=ty):
                    raise ValueError("A local lemma needs one proof subgoal matching its statement.")
                block=[pad+"have "+h+" : "+ty+" := by"]
                body,body_trace,_=emit_sequence(subgoals[0].get("steps"),known,depth+1,False,case_depth)
                lines_out.extend(block);trace_out.extend(block)
                lines_out.extend(body);trace_out.extend(body_trace)
                known.add(h);introduced.append(h)
                if trace_scope:
                    trace_out.append(pad+"duet_trace "+h)
                continue
            if kind=="obtain":
                h,evidence,copy,premise=(step.get(k) for k in ("name","evidenceName","copy","source"))
                if any(not isinstance(n,str) or not re.fullmatch(_SIMPLE,n) for n in (h,evidence,copy,premise)):
                    raise ValueError("Expected simple existential binding names.")
                if len({h,evidence,copy,premise})!=4 or any(n in known for n in (h,evidence,copy)):
                    raise ValueError("Existential binding names must be fresh and distinct.")
                ty,evidence_ty=step.get("type"),step.get("evidenceType")
                annotation(ty,"a restricted existential witness type")
                annotation(evidence_ty,"a restricted existential evidence type")
                block=["have "+copy+" := "+premise,"rcases "+copy+" with ⟨"+h+", "+evidence+"⟩",
                       "change "+ty+" at "+h,"change "+evidence_ty+" at "+evidence]
                for line in block:
                    lines_out.append(pad+line);trace_out.append(pad+line)
                if trace_scope:
                    trace_out.extend([pad+"duet_trace_object "+h,pad+"duet_trace "+evidence])
                known.update((h,evidence));introduced.extend((h,evidence))
                continue
            if kind in ("introduce","assume"):
                h,ty=step.get("name"),step.get("type")
                if not isinstance(h,str) or not re.fullmatch(_SIMPLE,h) or h in known:
                    raise ValueError("Invalid or repeated introduction name.")
                annotation(ty,"an introduction type")
                block=["intro "+h,"change "+ty+" at "+h]
                for line in block:
                    lines_out.append(pad+line);trace_out.append(pad+line)
                if trace_scope:
                    trace_out.append(pad+("duet_trace " if kind=="assume" else "duet_trace_object ")+h)
                known.add(h);introduced.append(h)
                continue
            if kind=="define":
                h,ty,value=step.get("name"),step.get("type"),step.get("value")
                if not isinstance(h,str) or not re.fullmatch(_SIMPLE,h) or h in known:
                    raise ValueError("Invalid or repeated local definition name.")
                for expression in (ty,value):
                    if (not isinstance(expression,str) or not expression.strip() or len(expression)>2000 or
                        not re.fullmatch(r"[\w'().,: +*/^=<>∀∃∈⊆↔→∧∨¬≤≥≠\-]+",expression) or
                        re.search(r"/-|--|:=|\b(?:by|sorry|admit|sorryAx|let|have|fun|match|do|where|import|theorem|def)\b",expression)):
                        raise ValueError("Expected a restricted local definition expression.")
                add("let "+h+" : "+ty+" := "+value)
                if trace_scope:
                    trace_out.append(pad+"duet_trace_object "+h)
                known.add(h);introduced.append(h)
                continue
            if kind=="establish":
                h,ty,app=step.get("name"),step.get("type"),step.get("application")
                if not isinstance(h,str) or not re.fullmatch(_SIMPLE,h) or h in known:
                    raise ValueError("Invalid or repeated intermediate name.")
                annotation(ty,"a single proposition annotation or an inferred type",optional=True)
                if not _ordered_application(app):
                    raise ValueError("Expected an ordered application of a named rule.")
                if app=="?" and ty is None:
                    raise ValueError("An intermediate proof hole requires an explicit proposition.")
                line="have "+h+(" : "+ty if ty is not None else "")+" := "+("by exact?" if app=="?" else app)
                add(line)
                if trace_scope:
                    trace_out.append(pad+"duet_trace "+h)
                known.add(h);introduced.append(h)
                continue
            raise ValueError("The chain must conclude exactly once, at its last step.")
        return lines_out,trace_out,introduced

    if not isinstance(steps,list) or not 1<=len(steps)<=16:
        raise ValueError("Use 1–16 proof steps.")
    emitted,emitted_trace,names=emit_sequence(steps,set(),1)
    lines=["by"]+emitted
    traced=["by"]+emitted_trace
    term=_safe_proof("\n".join(lines))
    instrumented=_safe_proof("\n".join(traced))
    args=" ".join(json.dumps(x,ensure_ascii=False) for x in (path,instrumented))
    result=_run_lean("import Lean\n"+source.rstrip()+"\n\n"+_adapter()+
                     "\n#duet_patch "+name+" "+args+"\n",project,trace=True)
    bindings=result["bindings"]
    if [b.get("name") for b in bindings]!=names:
        raise ValueError("Lean did not return the expected ordered intermediate bindings.")
    return {"term":term,"bindings":bindings,"goal":result["localType"],"status":"inferred",
            "note":"Local elaboration and rebuilt expression checked; export still requires independent validation."}

def abstract_preview(source, path, project=None):
    """Abstract the selected proof and independently check its standalone export."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path,str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}",path):
        raise ValueError("Invalid proof node path.")
    args=json.dumps(path,ensure_ascii=False)
    adapter=_adapter()
    result=_run_lean("import Lean\n"+source.rstrip()+"\n\n"+adapter+"\n#duet_abstract "+name+" "+args+"\n",project)
    result["standaloneChecked"]=False
    result["exportShapePreserved"]=False
    result["source"]=None
    prelude=source[:NAME.search(source).start()]
    if result.get("universes"):
        result["exportNote"]="Closed proof checked. Standalone universe-polymorphic export is not supported yet."
        return result
    if any(line.strip() and not re.fullmatch(r"import\s+\S.*",line) for line in prelude.splitlines()):
        result["exportNote"]="Closed proof checked. Standalone export requires an imports-only prelude."
        return result
    other="LeanDuetExtractedLemma"
    if re.search(r"\b"+other+r"\b",source):
        result["exportNote"]="Closed proof checked. Preview declaration name collides with source."
        return result
    candidate=_candidate(other,result["type"],result["term"],prelude)
    try:
        _run_lean(candidate+'\n#eval "LEANDUET_EXPORT_OK"\n',project,"LEANDUET_EXPORT_OK")
        result["standaloneChecked"]=True
        renamed=_candidate(other,result["type"],result["term"],"")
        _run_lean("import Lean\n"+source.rstrip()+"\n\n"+renamed+"\n"+adapter+
                  "\n#duet_compare_abstraction "+name+" "+other+" "+args+"\n",project,"LEANDUET_ABSTRACTION_MATCH")
    except ValueError as exc:
        result["exportNote"]="Closed proof checked, but standalone structural export was not certified: "+str(exc)
        return result
    result["source"]=candidate
    result["exportShapePreserved"]=True
    result["exportNote"]="Standalone theorem compiled and its elaborated proof shape matches the abstraction."
    return result

def factor_preview(source, path, project=None):
    """Produce a separately compiled two-theorem refactoring preview, never mutate input."""
    name=_name(source)
    result=abstract_preview(source,path,project)
    if not result["exportShapePreserved"] or not result["source"]:
        raise ValueError("Factoring requires a certified standalone lemma. "+result["exportNote"])
    lemma="LeanDuetExtractedLemma"
    other="LeanDuetFactoredPreview"
    if re.search(r"\b"+other+r"\b",source):
        raise ValueError("Reserved factored preview name.")
    prelude=source[:NAME.search(source).start()]
    lemma_body=_candidate(lemma,result["type"],result["term"],"")
    adapter=_adapter()
    args=json.dumps(path,ensure_ascii=False)
    prefix="import Lean\n"+source.rstrip()+"\n\n"+lemma_body+"\n"
    factored=_run_lean(prefix+adapter+"\n#duet_factor "+name+" "+lemma+" "+args+"\n",project)
    candidate=_safe_proof(prelude+lemma_body+"\n"+_candidate(name,factored["type"],factored["term"],""))
    _run_lean(candidate+'\n#eval "LEANDUET_FACTOR_EXPORT_OK"\n',project,"LEANDUET_FACTOR_EXPORT_OK")
    compare=_candidate(other,factored["type"],factored["term"],"")
    _run_lean(prefix+compare+"\n"+adapter+"\n#duet_compare_factor "+name+" "+other+" "+lemma+" "+args+"\n",project,"LEANDUET_FACTOR_MATCH")
    return {"source":candidate,"lemma":lemma,"path":path,"statementDefEq":True,
            "proofComplementPreserved":True,"lemmaShapePreserved":True,"standaloneChecked":True,
            "note":"Both declarations compiled independently; the original proof complement and extracted call match the expected structural edit."}

def inspect_ir(source, path, formula="", project=None):
    """Export a revision-local typed judgment as structural kernel syntax."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path,str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}",path):
        raise ValueError("Invalid proof node path.")
    if not isinstance(formula,str) or len(formula)>4000 or re.search(r"[\r\n;{}]|/-|--|:=|\b(?:by|sorry|admit)\b",formula):
        raise ValueError("Expected a single formula expression.")
    args=" ".join(json.dumps(x,ensure_ascii=False) for x in (path,formula))
    result=_run_lean("import Lean\n"+source.rstrip()+"\n\n"+_adapter()+"\n#duet_ir "+name+" "+args+"\n",project)
    if result.get("format")!="leanduet.kernel-judgment" or result.get("schema")!=1:
        raise ValueError("Unexpected semantic IR format.")
    return result

def search(source, path, rule="", project=None, required=None, formula=""):
    """Discover locally closed proof candidates from Lean's loaded environment."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path, str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}", path):
        raise ValueError("Invalid proof node path.")
    if not isinstance(rule, str) or (rule and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]{0,159}", rule)):
        raise ValueError("Use an exact declaration name or automatic type search.")
    required = [] if required is None else required
    if not isinstance(required,list) or len(required)>8 or any(
        not isinstance(n,str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']{0,63}",n)
        for n in required
    ) or len(set(required))!=len(required):
        raise ValueError("Specify at most eight distinct, simple local premise names.")
    if not isinstance(formula,str) or len(formula)>4000 or re.search(r"[\r\n;{}]|/-|--|:=|\b(?:by|sorry|admit)\b",formula):
        raise ValueError("Expected a single formula expression.")
    args = " ".join(json.dumps(x,ensure_ascii=False) for x in (path,rule,",".join(required),formula))
    return _run_lean("import Lean\n" + source.rstrip() + "\n\n" + _adapter() +
                     "\n#duet_search " + name + " " + args + "\n", project)

def interpret(source,path,alternatives,project=None):
    """Bounded batch of local candidate checks; no source mutation or AI execution."""
    name=_name(source)
    _safe_proof(source)
    if not isinstance(path,str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}",path):
        raise ValueError("Invalid proof node path.")
    if not isinstance(alternatives,list) or not 1<=len(alternatives)<=8:
        raise ValueError("Use 1–8 interpretations.")
    rows=[]
    for a in alternatives:
        if not isinstance(a,dict):
            raise ValueError("Invalid interpretation.")
        f,r,t=a.get("formula",""),a.get("rule",""),a.get("term","")
        p=a.get("required",[])
        if not isinstance(f,str) or len(f)>4000 or re.search(r"[\r\n;{}]|/-|--|:=|\b(?:by|sorry|admit)\b",f):
            raise ValueError("Invalid formula.")
        if not isinstance(r,str) or (r and not re.fullmatch(_RULE,r)):
            raise ValueError("Invalid rule.")
        if not isinstance(p,list) or len(p)>8 or any(not isinstance(x,str) or not re.fullmatch(_SIMPLE,x) for x in p) or len(set(p))!=len(p):
            raise ValueError("Invalid premises.")
        # This endpoint is deliberately limited to simple explicit applications.
        # Arbitrary Lean fragments remain in the user-initiated patch editor.
        if not isinstance(t,str) or (t and (not re.fullmatch(_RULE+r"(?: "+_SIMPLE+r"){0,8}",t) or re.search(r"\b(?:sorry|admit|sorryAx|by)\b",t))) or (t and r):
            raise ValueError("Invalid explicit application.")
        rows.append({"formula":f,"rule":r,"required":",".join(p),"term":t})
    args=" ".join(json.dumps(x,ensure_ascii=False) for x in (path,json.dumps(rows,ensure_ascii=False)))
    return _run_lean("import Lean\n"+source.rstrip()+"\n\n"+_adapter()+"\n#duet_interpret "+name+" "+args+"\n",project)

def informath(source, project=None):
    """Reuse the upstream CLI as an external, separately installed tool."""
    root = os.environ.get("LEANDUET_INFORMATH_ROOT")
    executable = os.environ.get("LEANDUET_INFORMATH_BIN", "RunInformath")
    if not root or not Path(root).is_dir() or not shutil.which(executable):
        raise ValueError("Install Informath separately and set LEANDUET_INFORMATH_ROOT and optionally LEANDUET_INFORMATH_BIN.")
    if project:
        raise ValueError("Informath project-mode interoperability is not yet implemented. Use a standalone proof.")
    # Upstream's current Lean exporter targets a newer Lean version. The user
    # must provide a compatible upstream installation and toolchain.
    with tempfile.TemporaryDirectory(prefix="leanduet-informath-") as directory:
        path = Path(directory) / "Proof.lean"
        path.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        if os.environ.get("LEANDUET_INFORMATH_TOOLCHAIN"):
            env["ELAN_TOOLCHAIN"] = os.environ["LEANDUET_INFORMATH_TOOLCHAIN"]
        r = subprocess.run([executable, "-from-formalism=lean", "-proof-text", str(path)],
                           cwd=Path(root).resolve(), env=env, capture_output=True, text=True,
                           encoding="utf-8", errors="replace", timeout=90)
    if r.returncode:
        raise ValueError("Informath failed:\n" + r.stderr[-3000:])
    if not r.stdout.strip() or len(r.stdout.encode()) > MAX_OUTPUT:
        raise ValueError("Informath returned empty or oversized output.")
    return {"narrative": r.stdout, "provider": "Informath", "verifiedAlignment": False}
