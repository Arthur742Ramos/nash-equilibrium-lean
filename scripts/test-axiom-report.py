"""Exercise the fail-closed audit independently of the Lean build."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
config = json.loads((root / "comparator.json").read_text())
names = config["theorem_names"] + [
    "Brouwer_Product",
    "NashEquilibrium.exists_nashMap_fixedPoint",
    "NashEquilibrium.exists_mixedNash",
]
lines = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
         for name in names]
valid = ''.join(lines)
cases = {
    "complete approved reports": (valid, True),
    "unknown axiom": (valid.replace('propext', 'unexpectedAxiom', 1), False),
    "sorry axiom": (valid.replace('propext', 'sorryAx', 1), False),
    "missing declaration": (''.join(lines[1:]), False),
    "duplicate declaration": (valid + lines[0], False),
    "unexpected declaration": (valid + "'extra' depends on axioms: []\n", False),
    "unrecognized output": (valid + 'warning: unexpected output\n', False),
    "empty report": ('', False),
}
for label, (report, success) in cases.items():
    result = subprocess.run(
        [sys.executable, str(root / 'scripts/check-axiom-report.py'),
         str(root / 'comparator.json')],
        input=report, text=True, capture_output=True,
    )
    if (result.returncode == 0) != success:
        sys.exit(f"FAIL {label}: {result.stdout}{result.stderr}")
print(f"Axiom parser regression tests passed ({len(cases)} cases).")
