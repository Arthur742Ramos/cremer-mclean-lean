"""Validate intake configuration and enable both bundled kernels for replay.

Palomar rejects submitter-provided kernel commands and injects its own in a
protected configuration. This standard preflight retains the authored module
names and writes an execution-only configuration outside the submitted tree.
It is not the production verifier's canonical-Challenge provenance audit.
"""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PIN = "65f0154ed776cd26c224254aa57b379137f28b0d"
parser = argparse.ArgumentParser()
parser.add_argument("destination", type=Path)
args = parser.parse_args()
contract = Path(os.environ.get("PALOMAR_SUBMISSION_DIR",
    ROOT.parent / "review-sources/PalomarSubmission")).resolve()
assert subprocess.check_output(["git", "-C", str(contract), "rev-parse", "HEAD"],
    text=True).strip() == PIN, "Unexpected Palomar policy revision"
sys.path.insert(0, str(contract))
from scripts.verify_submission import load_comparator_config

config = load_comparator_config(ROOT / "comparator.json")
prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
    cwd=ROOT, text=True).strip()).resolve()
kernels = {name: [str(prefix / "bin" / binary)]
    for name, binary in (("nanoda", "nanoda_bin"), ("con-ron", "con-ron"))}
for command in kernels.values():
    assert Path(command[0]).is_file() and os.access(command[0], os.X_OK), command
destination = args.destination.resolve()
assert not destination.is_relative_to(ROOT), "Execution config must stay outside submission"
assert not args.destination.is_symlink(), "Execution config must not be a symlink"
config["external_kernels"] = kernels
destination.write_text(json.dumps(config, indent=2) + "\n")
print("Official Palomar comparator configuration validator: PASS")
print("Execution-only configuration enables bundled NanoDa and con-ron")
