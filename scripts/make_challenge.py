"""Generate genuine definitions and exact selected theorem statements.

Only the six comparator-selected Challenge theorem proofs are deliberate holes.
Complete proofs remain in the unchanged Border library imported by Solution.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATEMENT_MODULES = {
    "border_feasibility": "Theorem",
    "feasible_iff_conditional": "Support",
    "border_conditional_feasibility": "Support",
    "independent_border_feasibility": "Independent",
    "independent_border_conditional_feasibility": "Independent",
    "allocation_le_one": "Support",
}


def render():
    config = json.loads((ROOT / "comparator.json").read_text())
    auction = (ROOT / "Border/Auction.lean").read_text()
    # Keep definition source bytes, except its closing namespace terminator.
    assert auction.endswith("end Border\n")
    definitions = auction.removesuffix("end Border\n")
    module_doc = """/-!
Compact comparison surface for Border's finite auction feasibility theorem.
All ten definitions below are genuine, with their exact library bodies.
Only the six comparator-selected theorem proofs are deliberate statement holes.
The complete, independently reviewed proofs are in Border, imported by Solution.
The official comparator checks their exact contracts; dependency auditing and
three-kernel passes check the complete Solution rather than these placeholders.
-/
"""
    # Lean requires imports before module documentation.
    insertion = definitions.index("\n@[expose]")
    definitions = definitions[:insertion] + "\n" + module_doc + definitions[insertion:]
    statements = []
    for qualified in config["theorem_names"]:
        name = qualified.removeprefix("Border.")
        module = STATEMENT_MODULES[name]
        source = (ROOT / "Border" / f"{module}.lean").read_text()
        matches = re.findall(r"(?m)^theorem " + re.escape(name) + r"\b[\s\S]*?:=", source)
        assert len(matches) == 1, qualified
        statement = matches[0]
        if name == "allocation_le_one":
            statement = "omit [∀ i, Fintype (T i)] in\n" + statement
        statements.append(
            f"/- Statement copied from Border/{module}.lean; complete proof in Solution. -/\n"
            + statement + " by\n  sorry\n"
        )
    return definitions + "\n" + "\n".join(statements) + "\nend Border\n"

if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(render())
