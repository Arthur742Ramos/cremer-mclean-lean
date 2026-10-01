"""Audit the intentionally incomplete reference separately from the Solution."""
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
config = json.loads((ROOT / "comparator.json").read_text())
selected = config["theorem_names"] + config["definition_names"]
source = "module\npublic import Challenge\n" + "".join(
    f"#print axioms {name}\n" for name in selected
)
with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="border-reference-", delete=False) as handle:
    handle.write(source)
    path = Path(handle.name)
try:
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                            text=True, capture_output=True, check=True)
finally:
    path.unlink()
rows = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout))
assert set(rows) == set(selected), rows
permitted = set(config["permitted_axioms"])
for name in selected:
    used = set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", rows[name]))
    if name in config["theorem_names"]:
        assert "sorryAx" in used and used <= permitted | {"sorryAx"}, (name, used)
    else:
        assert used <= permitted, (name, used)
(ROOT / "evidence/challenge-reference-axioms.log").write_text(result.stdout)
print("Reference audit: exactly six selected theorem placeholders; all ten definitions genuine")
