#!/usr/bin/env bash
# Verification script for the formalization of
#   "On the polynomial values represented by quadratic forms" (B. Grechuk, J. Agbanwa).
#
# The verification covers the entry modules and every Lean source in RequestProject/:
#   RequestProject.lean  imports the development in RequestProject/Main.lean,
#   Challenge.lean       self-contained statements of the main results,
#   Solution.lean        proofs of every Challenge statement.
#
# It (1) builds the project and checks that every file elaborates without errors *or warnings*,
# (2) checks the sources for `sorry`, `admit`, user-declared `axiom`s and `@[implemented_by]`,
# and (3) prints the axiom dependencies of every name listed in `comparator.json`.

set -uo pipefail

cd "$(dirname "$0")"

files=()
while IFS= read -r f; do
  files+=("$f")
done < <(find RequestProject -type f -name '*.lean' -print | sort)
files+=(RequestProject.lean Challenge.lean Solution.lean)

status=0

echo "== 1/3  Building =="
if ! lake build; then
  echo "FAIL: lake build failed."
  exit 1
fi
echo "OK: build succeeded."

for f in "${files[@]}"; do
  if ! diagnostics=$(lake env lean -DwarningAsError=true "$f" 2>&1); then
    echo "$diagnostics"
    echo "FAIL: $f failed to elaborate."
    status=1
  elif [ -n "$diagnostics" ]; then
    echo "$diagnostics"
    echo "FAIL: $f produced diagnostics (errors or warnings)."
    status=1
  else
    echo "OK: $f elaborates with no errors and no warnings."
  fi
done
echo

echo "== 2/3  Scanning the sources =="
pattern='\bsorry\b|\badmit\b|^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]|@\[implemented_by|native_decide'
if grep -nE "$pattern" "${files[@]}" | grep -v '^RequestProject/Main.lean:[0-9]*:\* No use of `native_decide`'; then
  echo "FAIL: forbidden constructs found above."
  status=1
else
  echo "OK: no sorry / admit / axiom / @[implemented_by] / native_decide in the sources."
fi
echo

echo "== 3/3  Checking axiom dependencies =="
if ! names=$(python3 - <<'PYCONFIG'
import json
with open("comparator.json") as f:
    config = json.load(f)
names = config["definition_names"] + config["theorem_names"]
if not names or not all(isinstance(n, str) and all(p.isidentifier() for p in n.split(".")) for n in names):
    raise SystemExit("Invalid or empty verification target list")
print("\n".join(dict.fromkeys(names)))
PYCONFIG
); then
  echo "FAIL: invalid verification manifest."
  exit 1
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  echo "import RequestProject"
  echo "import Challenge"
  echo "import Solution"
  echo "set_option pp.width 100000"
  for n in $names; do
    echo "#print axioms $n"
  done
} > "$tmp/AxiomCheck.lean"

if ! lake env lean "$tmp/AxiomCheck.lean" > "$tmp/axioms.txt" 2>&1; then
  cat "$tmp/axioms.txt"
  echo "FAIL: could not check all names."
  status=1
elif ! python3 - "$tmp/axioms.txt" "$names" <<'PYAXIOMS'
import json
import re
import sys
from pathlib import Path
with open("comparator.json") as f:
    allowed = set(json.load(f)["allowed_axioms"])
standard = {"propext", "Classical.choice", "Quot.sound"}
if not allowed <= standard:
    raise SystemExit("FAIL: manifest permits a non-standard axiom")
output = Path(sys.argv[1]).read_text()
print(output, end="")
seen = set()
for line in output.splitlines():
    match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
    if match:
        name, axioms = match.groups()
        forbidden = {a.strip() for a in axioms.split(",") if a.strip()} - allowed
        if forbidden:
            raise SystemExit(f"FAIL: {name} uses forbidden axioms: {sorted(forbidden)}")
        seen.add(name)
    else:
        match = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if not match:
            raise SystemExit(f"FAIL: unexpected axiom-check output: {line}")
        seen.add(match.group(1))
missing = set(sys.argv[2].splitlines()) - seen
if missing:
    raise SystemExit(f"FAIL: missing axiom checks: {sorted(missing)}")
print("OK: every listed declaration uses only permitted standard axioms.")
PYAXIOMS
then
  status=1
fi
echo

if [ "$status" -eq 0 ]; then
  echo "ALL CHECKS PASSED"
else
  echo "SOME CHECKS FAILED"
fi
exit "$status"
