"""Generate Challenge.lean: genuine definitions, exact comparator theorem statements.

Only the comparator-selected theorem proofs are deliberate holes (sorry).
Complete proofs remain in the unchanged CremerMcLean library imported by Solution.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def render():
    config = json.loads((ROOT / "comparator.json").read_text())
    src = (ROOT / "CremerMcLean" / "Basic.lean").read_text()
    # Replace each comparator theorem's proof body with a deliberate sorry hole.
    # The statement (through ':=') is kept byte-identical to the library.
    for qualified in config["theorem_names"]:
        name = qualified.removeprefix("CremerMcLean.")
        m = re.search(r"(?m)^theorem " + re.escape(name) + r"\b[\s\S]*?:=", src)
        assert m, qualified
        body_start = m.end()
        nxt = re.search(
            r"(?m)^(?:theorem |noncomputable def |def |end\b)", src[body_start:]
        )
        body_end = body_start + nxt.start() if nxt else len(src)
        src = src[:body_start] + " by\n  sorry\n" + src[body_end:]
    module_doc = """/-!
Compact comparison surface for the Cremer-McLean full surplus extraction theorem.
All definitions below are genuine, with their exact library bodies.
Only the three comparator-selected theorem proofs are deliberate statement holes.
The complete, mechanically checked proofs are in CremerMcLean, imported by Solution.
They were developed with AI assistance and then independently compiled,
audited for placeholders and axioms, and comparator-checked; no separate
independent human review of the proofs was performed.
The official comparator checks their exact contracts; dependency auditing and
three-kernel passes check the complete Solution rather than these placeholders.
-/
"""
    idx = src.index("/-!")
    src = src[:idx] + module_doc + "\n" + src[idx:]
    return src


if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(render())
    print("wrote Challenge.lean")
