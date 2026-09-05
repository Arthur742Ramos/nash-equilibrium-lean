"""Fail closed on missing reports, unexpected output, or unapproved axioms."""
import json
import re
import sys

config = json.load(open(sys.argv[1], encoding="utf-8"))
allowed = set(config["permitted_axioms"])
expected = set(config["theorem_names"]) | {
    "Brouwer_Product",
    "NashEquilibrium.exists_nashMap_fixedPoint",
    "NashEquilibrium.exists_mixedNash",
}
text = sys.stdin.read()
pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
seen = set()
for match in pattern.finditer(text):
    name, body = match.groups()
    if name in seen:
        sys.exit(f"error: duplicate axiom report for {name}")
    seen.add(name)
    unexpected = {a.strip() for a in body.split(',') if a.strip()} - allowed
    if unexpected:
        sys.exit(f"error: {name} uses unapproved axioms: {sorted(unexpected)}")
if pattern.sub('', text).strip():
    sys.exit("error: unrecognized axiom report output")
if seen != expected:
    sys.exit(f"error: axiom report coverage mismatch: missing={expected-seen}, extra={seen-expected}")
print(f"Exact axiom allowlist passed for {len(seen)} declarations.")
