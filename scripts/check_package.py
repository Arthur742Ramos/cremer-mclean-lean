"""Fail closed on contract drift and holes outside named Challenge statements."""
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
cfg = json.loads((ROOT / "comparator.json").read_text())
assert set(cfg) == {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms"}
assert cfg["challenge_module"] == "Challenge" and cfg["solution_module"] == "Solution"
assert set(cfg["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
assert len(cfg["theorem_names"]) == 3
original = (ROOT / "Challenge.lean").read_bytes()
from make_challenge import render
assert original == render().encode(), "Challenge differs from the reviewed generated source"
assert len(original) <= 100 * 1024 and len(original.splitlines()) <= 1000
for file in [*ROOT.glob("*.lean"), *ROOT.glob("CremerMcLean/*.lean")]:
    content = file.read_text()
    assert content.startswith("module\n"), file
    if file.name == "Challenge.lean" and file.parent == ROOT:
        # Generation equality above restricts placeholders to precisely the
        # three official comparator-selected Challenge theorem proof bodies.
        assert len(re.findall(r"(?m)^  sorry$", content)) == len(cfg["theorem_names"]) == 3
        checked_content = re.sub(r"(?m)^  sorry$", "", content)
    else:
        checked_content = content
    assert not re.search(r"\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|ofReduceBool)\b", checked_content), file
    assert len(content.splitlines()) <= 10000, file
for name in cfg["definition_names"]:
    assert re.search(r"\bdef\s+" + re.escape(name.removeprefix("CremerMcLean.")) + r"\b", original.decode()), name
assert all(re.search(r"\btheorem\s+" + re.escape(n.removeprefix("CremerMcLean.")) + r"\b", original.decode())
           for n in cfg["theorem_names"])
print(f"Package shape: PASS; Challenge {len(original.splitlines())} lines, {len(original)} bytes; three named statement holes; complete library/Solution")

axioms = ROOT / "evidence/final-axioms.log"
if axioms.exists():
    rows = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", axioms.read_text()))
    noax = set(re.findall(r"'([^']+)' does not depend on any axioms", axioms.read_text()))
    assert not (set(rows) & noax), "duplicate axiom rows"
    rows.update({name: "" for name in noax})
    selected = cfg["theorem_names"] + cfg["definition_names"]
    assert set(selected) <= rows.keys(), set(selected) - rows.keys()
    for name, used in rows.items():
        assert set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", used)) <= set(cfg["permitted_axioms"]), (name, used)
    print("All selected declarations and internal proof milestones use only the three standard axioms")

files = [*ROOT.glob("*.lean"), *ROOT.glob("CremerMcLean/*.lean"), ROOT / "lakefile.toml",
         ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "comparator.json"]
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
record = {
    "source_files_sha256": hashes,
    "lean": (ROOT / "lean-toolchain").read_text().strip(),
    "mathlib": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
    "comparison": "three exact theorem statements with named Challenge holes; fifteen genuine unchanged definitions; complete Solution proofs",
    "verification_kernels": ["Lean default", "nanoda", "con-ron"],
}
manifest = ROOT / "evidence/verification-manifest.json"
if "--record" in sys.argv:
    record["recorded_at_utc"] = datetime.now(timezone.utc).isoformat()
    record["local_platform"] = "macOS arm64; Comparator without Linux bubblewrap"
    manifest.write_text(json.dumps(record, indent=2) + "\n")
else:
    assert manifest.exists(), "Missing verification manifest; use --record after validation"
    saved = json.loads(manifest.read_text())
    for key, value in record.items():
        assert saved[key] == value, ("Verification manifest mismatch", key)
    print("Recorded source hashes match the exact current source")
