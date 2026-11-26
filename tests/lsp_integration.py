"""Native completion smoke test against the pinned Lean toolchain."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from lean_lsp import complete
source="def completionDemo := Nat.suc\n"
r=complete(source,0,len(source.splitlines()[0]))
assert r["provider"]=="Lean LSP",r
assert any("succ" in item["label"] for item in r["items"]),r
print("Native Lean language server returned identifier completion")
