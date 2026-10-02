"""Check actual authors, classifications and selected statement alignment."""
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
policy = Path(os.environ.get("PALOMAR_SUBMISSION_DIR", ROOT.parent / "review-sources/PalomarSubmission")).resolve()
sys.path.insert(0, str(policy))
from scripts.submission_contract import load_formalization_metadata

metadata = load_formalization_metadata(ROOT / "formalization.yaml")
authors = ["Arthur Freitas Ramos", "David Barros Hulak", "Ruy Jose Guerra Barretto de Queiroz"]
assert metadata["project"]["authors"] == authors
assert metadata["project"]["responsible_maintainers"] == authors
assert metadata["project"]["license"] == "BSD-3-Clause"
cfg = json.loads((ROOT / "comparator.json").read_text())
assert [s["lean"] for s in metadata["alignment"]["statements"]] == cfg["theorem_names"]
assert metadata["classification"]["msc2020"] == ["91B26"]
import yaml
citation = yaml.safe_load((ROOT / "CITATION.cff").read_text())
assert [a["given-names"] + " " + a["family-names"] for a in citation["authors"]] == authors
assert all(a in (ROOT / "README.md").read_text() for a in authors)
print("Official formalization metadata validator and author/alignment checks: PASS")
