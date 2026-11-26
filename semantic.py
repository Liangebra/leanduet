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

def extract(source, project=None):
    name = _name(source)
    if re.search(r"\b(?:sorry|admit|sorryAx)\b", source):
        raise ValueError("Incomplete proofs cannot be inspected as verified derivations.")
    command = ["lake", "env", "lean"] if project else ["lean"]
    if not shutil.which(command[0]):
        raise ValueError("Lean toolchain not available.")
    adapter = (ROOT / "lean" / "Extract.lean").read_text(encoding="utf-8")
    # This is a separate elaboration with an extra metaprogramming import.
    # It is not a substitute for checking the original source.
    text = "import Lean\n" + source.rstrip() + "\n\n" + adapter + "\n#duet_extract " + name + "\n"
    with tempfile.TemporaryDirectory(prefix="leanduet-structure-") as directory:
        path = Path(directory) / "Inspect.lean"
        path.write_text(text, encoding="utf-8")
        r = subprocess.run(command + [str(path)], cwd=project or ROOT, capture_output=True,
                           text=True, encoding="utf-8", errors="replace", timeout=45)
    out = r.stdout + r.stderr
    if r.returncode or re.search(r"\bsorry\b", out):
        raise ValueError("Semantic extraction failed:\n" + out[-3000:])
    for line in out.splitlines():
        if "LEANDUET_JSON:" in line:
            raw = line.split("LEANDUET_JSON:", 1)[1]
            if len(raw.encode()) > MAX_OUTPUT:
                raise ValueError("Proof tree exceeds the current inspection limit.")
            return json.loads(raw)
    raise ValueError("No semantic result was produced.")

def informath(source, project=None):
    """Reuse the upstream CLI as an external, separately installed tool."""
    root = os.environ.get("LEANDUET_INFORMATH_ROOT")
    executable = os.environ.get("LEANDUET_INFORMATH_BIN", "RunInformath")
    if not root or not Path(root).is_dir() or not shutil.which(executable):
        raise ValueError("Install Informath separately and set LEANDUET_INFORMATH_ROOT and optionally LEANDUET_INFORMATH_BIN.")
    # Upstream's current Lean exporter targets a newer Lean version. The user
    # must provide a compatible upstream installation and toolchain.
    with tempfile.TemporaryDirectory(prefix="leanduet-informath-") as directory:
        path = Path(directory) / "Proof.lean"
        path.write_text(source, encoding="utf-8")
        r = subprocess.run([executable, "-from-formalism=lean", "-proof-text", str(path)],
                           cwd=Path(root).resolve(), capture_output=True, text=True,
                           encoding="utf-8", errors="replace", timeout=90)
    if r.returncode:
        raise ValueError("Informath failed:\n" + r.stderr[-3000:])
    if not r.stdout.strip() or len(r.stdout.encode()) > MAX_OUTPUT:
        raise ValueError("Informath returned empty or oversized output.")
    return {"narrative": r.stdout, "provider": "Informath", "verifiedAlignment": False}
