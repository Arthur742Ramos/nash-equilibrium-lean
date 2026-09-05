#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

for required_file in \
  lean-toolchain lake-manifest.json formalization.yaml Challenge.lean Solution.lean \
  comparator.json LICENSE THIRD_PARTY_NOTICES.md; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (root / name).exists()]
if len(lakefiles) != 1:
    raise SystemExit(f"error: expected one Lakefile, found {lakefiles}")

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds the 100 KiB or 1,000-line cap")
imports = [
    line.split()[1]
    for line in challenge_text.splitlines()
    if line.startswith("import ")
]
if imports != [
    "Mathlib.Data.Finset.Max",
    "Mathlib.Data.Fintype.Pi",
    "Mathlib.Algebra.BigOperators.GroupWithZero.Finset",
    "Mathlib.Algebra.Order.BigOperators.Group.Finset",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Tactic",
]:
    raise SystemExit(f"error: Challenge.lean has an unexpected direct Mathlib import list: {imports}")

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is invalid: {error}")
required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
allowed = required | {"definition_names", "enable_nanoda"}
if not isinstance(comparator, dict) or set(comparator) - allowed or not required <= set(comparator):
    raise SystemExit("error: comparator.json has an invalid key set")
if comparator["challenge_module"] != "Challenge":
    raise SystemExit("error: comparator.json must use Challenge as its statement module")
if comparator["solution_module"] != "Solution":
    raise SystemExit("error: comparator.json must use Solution as its proof module")
if comparator["theorem_names"] != [
    "NashEquilibrium.Palomar.exists_nash_maximizing_ordinal_potential",
    "NashEquilibrium.Palomar.isNash_iff_potential_local_maximum",
    "NashEquilibrium.Palomar.no_betterResponse_cycle_of_generalized_ordinal_potential",
    "NashEquilibrium.Palomar.weaklyAcyclic_of_generalized_ordinal_potential",
    "NashEquilibrium.Palomar.mixedNash_support_payoff_eq",
    "NashEquilibrium.Palomar.exists_mixedNash",
]:
    raise SystemExit("error: comparator surface must select the six pure/mixed theorems")
if comparator.get("enable_nanoda") is not True:
    raise SystemExit("error: comparator.json must enable NanoDa")
if not set(comparator["permitted_axioms"]) <= {
    "propext",
    "Quot.sound",
    "Classical.choice",
}:
    raise SystemExit("error: comparator.json contains an unsupported axiom")

solution = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", solution):
    raise SystemExit("error: Solution.lean contains a proof placeholder")
if re.search(r"^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: Solution.lean declares an axiom or unsafe definition")

for path in sorted(p for directory in ("NashEquilibrium", "Gametheory")
                   for p in (root / directory).rglob("*.lean")):
    text = path.read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", text):
        raise SystemExit(f"error: proof placeholder found in {path.relative_to(root)}")
    if re.search(r"^\s*(axiom|unsafe)\b", text, re.MULTILINE):
        raise SystemExit(f"error: axiom or unsafe declaration found in {path.relative_to(root)}")

print(f"Palomar package shape passed: Challenge {challenge.stat().st_size} bytes")
PY

challenge_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *)
      echo "error: Challenge import closure contains a non-allowlisted source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$challenge_dependencies"

challenge_holes=$(grep -Ec '^[[:space:]]*sorry[[:space:]]*$' Challenge.lean || true)
if [ "$challenge_holes" -ne 2 ]; then
  echo "error: Challenge.lean must contain exactly two deliberate statement proof holes" >&2
  exit 1
fi

lake build
lake env lean --src-deps Solution.lean >/dev/null
python3 scripts/test-axiom-report.py
axiom_report=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf '%s\n' "$axiom_report"
printf '%s\n' "$axiom_report" | python3 scripts/check-axiom-report.py comparator.json

ruby -ryaml - "$repository_root/formalization.yaml" <<'RUBY'
path = ARGV.fetch(0)
data = YAML.safe_load(File.read(path), aliases: false)
abort "error: formalization.yaml must be a mapping" unless data.is_a?(Hash)
abort "error: metadata version must be v0.4" unless data["version"] == "v0.4"
project = data["project"]
abort "error: project metadata is incomplete" unless project.is_a?(Hash)
abort "error: project.name is missing" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "error: project.description is missing" unless project["description"].is_a?(String) && !project["description"].strip.empty?
abort "error: project.authors is empty" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "error: project.responsible_maintainers is empty" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "error: project.license must match the root LICENSE" unless project["license"] == "BSD-3-Clause"
notices_path = File.join(File.dirname(path), "THIRD_PARTY_NOTICES.md")
abort "error: third-party MIT notice is missing" unless File.file?(notices_path) && File.read(notices_path).include?("MIT License")
classification = data["classification"]
abort "error: classification is incomplete" unless classification.is_a?(Hash) && classification["arxiv"].is_a?(Array) && classification["msc2020"].is_a?(Array)
sources = data["sources"]
abort "error: sources must be a nonempty array" unless sources.is_a?(Array) && !sources.empty?
valid_source_relationships = %w[formalizes adapts independently-proves background other]
invalid_relationships = sources.map { |source| source["relationship"] }
  .reject { |relationship| valid_source_relationships.include?(relationship) }
  .uniq
abort "error: sources contain invalid relationships: #{invalid_relationships.join(', ')}" unless invalid_relationships.empty?
source_based_relationships = %w[formalizes adapts independently-proves]
abort "error: source-based results need a formalizes, adapts, or independently-proves source" unless sources.any? { |source| source_based_relationships.include?(source["relationship"]) }
abort "error: sources must cite the AFP entry" unless sources.any? { |source| source["id"] == "https://isa-afp.org/entries/Nash_Equilibrium.html" }
abort "error: automation metadata is incomplete" unless data["automation"].is_a?(Hash) && data["automation"]["methods"].is_a?(Array) && !data["automation"]["methods"].empty?
abort "error: review metadata is incomplete" unless data["review"].is_a?(Hash) && data["review"]["status"].is_a?(String)
puts "formalization.yaml shape passed."
RUBY

git diff --check
echo "Palomar preparation checks passed."
