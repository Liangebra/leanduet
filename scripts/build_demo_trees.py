"""Build read-only, exact-source demo trees using the pinned Lean toolchain."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from semantic import extract

def main():
    examples = json.loads(subprocess.check_output(
        ["node", "--input-type=module", "-e",
         "import {EXAMPLES} from './web/core.mjs'; console.log(JSON.stringify(EXAMPLES));"],
        cwd=ROOT, text=True, encoding="utf-8"))
    entries = []
    for example in examples:
        source = example["source"]
        result = extract(source, reading_only=True)
        if result.get("schema") != 1 or not isinstance(result.get("tree"), dict):
            raise ValueError("Invalid Lean extraction result for " + example["name"])
        entries.append({"source": source, "tree": result["tree"]})
    target = ROOT / "web" / "demo-proof-trees.json"
    target.write_text(json.dumps({
        "schema": 1,
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "entries": entries
    }, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8")
    print(f"Extracted {len(entries)} exact-source demo trees with Lean.")

if __name__ == "__main__":
    main()
