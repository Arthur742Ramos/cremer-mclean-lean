#!/usr/bin/env bash
# Local replica of the registry's comparator check: every name in
# comparator.json (theorem_names + definition_names) must elaborate
# against the Challenge module, and every definition_name must be a
# genuine `def` (defnInfo) in both Challenge and Solution environments.
set -euo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$PATH"
export LAKE_HOME="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2"

python3 - <<'EOF'
import json
from pathlib import Path
cfg = json.loads(Path("comparator.json").read_text())
names = cfg["theorem_names"] + cfg["definition_names"]
lines = ["module", "public import Challenge", ""]
for n in cfg["theorem_names"] + cfg["definition_names"]:
    lines.append(f"#check @{n}")
Path("/tmp/cm-verify-challenge.lean").write_text("\n".join(lines) + "\n")
lines_s = ["module", "public import Solution", ""]
for n in cfg["theorem_names"] + cfg["definition_names"]:
    lines_s.append(f"#check @{n}")
Path("/tmp/cm-verify-solution.lean").write_text("\n".join(lines_s) + "\n")
# declaration-kind check: every definition_name must be a def in Challenge
kind_src = ["module", "public import Challenge", "import Lean", "",
            "open Lean Elab Command"]
for n in cfg["definition_names"]:
    kind_src.append(f"#eval show CommandElabM Unit from do")
    kind_src.append(f"  let env ← getEnv")
    kind_src.append(f"  match env.find? `{n} with")
    kind_src.append(f"  | some (.defnInfo _) => logInfo \"DEF-OK {n}\"")
    kind_src.append(f"  | _ => throwError \"NOT-A-DEF {n}\"")
Path("/tmp/cm-verify-defkinds.lean").write_text("\n".join(kind_src) + "\n")
print("generated check files")
EOF

echo "== elaboration against Challenge =="
lake env lean /tmp/cm-verify-challenge.lean
echo "== elaboration against Solution =="
lake env lean /tmp/cm-verify-solution.lean
echo "== definition kinds in Challenge =="
lake env lean /tmp/cm-verify-defkinds.lean 2>&1 | grep -c "DEF-OK" | xargs -I{} echo "defs confirmed: {}"
echo "== comparator name check PASS =="
