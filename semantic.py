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

def _run_lean(text, project=None, marker=None):
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
        raise ValueError("Lean semantic check failed:\n" + out[-4000:])
    if marker:
        if marker not in out:
            raise ValueError("Lean did not confirm the required check.")
        return out
    for line in out.splitlines():
        if "LEANDUET_JSON:" in line:
            raw = line.split("LEANDUET_JSON:", 1)[1]
            if len(raw.encode()) > MAX_OUTPUT:
                raise ValueError("Proof tree exceeds the current inspection limit.")
            return json.loads(raw)
    raise ValueError("No semantic result was produced.")

def _adapter():
    return (ROOT / "lean" / "Extract.lean").read_text(encoding="utf-8")

def extract(source, project=None):
    name = _name(source)
    if re.search(r"\b(?:sorry|admit|sorryAx)\b", source):
        raise ValueError("Incomplete proofs cannot be inspected as verified derivations.")
    return _run_lean("import Lean\n" + source.rstrip() + "\n\n" + _adapter() +
                     "\n#duet_extract " + name + "\n", project)

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


def search(source, path, rule="", project=None):
    """Discover locally closed proof candidates from Lean's loaded environment."""
    name = _name(source)
    _safe_proof(source)
    if not isinstance(path, str) or not re.fullmatch(r"root(?:/(?:body|value|arg[0-9]+)){0,16}", path):
        raise ValueError("Invalid proof node path.")
    if not isinstance(rule, str) or (rule and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]{0,159}", rule)):
        raise ValueError("Use an exact declaration name or automatic type search.")
    args = " ".join(json.dumps(x,ensure_ascii=False) for x in (path,rule))
    return _run_lean("import Lean\n" + source.rstrip() + "\n\n" + _adapter() +
                     "\n#duet_search " + name + " " + args + "\n", project)

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
