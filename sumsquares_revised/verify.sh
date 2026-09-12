#!/usr/bin/env bash
# Verification script for the formalization of
#   "On the polynomial values represented by quadratic forms" (B. Grechuk, J. Agbanwa).
#
# The project has three Lean files:
#   RequestProject.lean  the development (namespaces PolyQF and PolyQF.Main),
#   Challenge.lean       self-contained statements of the main results,
#   Solution.lean        proofs of every Challenge statement.
#
# It (1) builds the project and checks that every file elaborates without errors *or warnings*,
# (2) checks the sources for `sorry`, `admit`, user-declared `axiom`s and `@[implemented_by]`,
# and (3) prints the axiom dependencies of every name listed in `comparator.json`.

set -uo pipefail

cd "$(dirname "$0")"

files="RequestProject.lean Challenge.lean Solution.lean"

status=0

echo "== 1/3  Building =="
if ! lake build; then
  echo "FAIL: lake build failed."
  exit 1
fi
echo "OK: build succeeded."

for f in $files; do
  diagnostics=$(lake env lean "$f" 2>&1)
  if [ -n "$diagnostics" ]; then
    echo "$diagnostics"
    echo "FAIL: $f produced diagnostics (errors or warnings)."
    status=1
  else
    echo "OK: $f elaborates with no errors and no warnings."
  fi
done
echo

echo "== 2/3  Scanning the sources =="
pattern='\bsorry\b|\badmit\b|^[[:space:]]*axiom[[:space:]]|@\[implemented_by|native_decide'
if grep -nE "$pattern" $files | grep -v '^RequestProject.lean:[0-9]*:\* No use of'; then
  echo "FAIL: forbidden constructs found above."
  status=1
else
  echo "OK: no sorry / admit / axiom / @[implemented_by] / native_decide in the sources."
fi
echo

echo "== 3/3  Checking axiom dependencies =="
names=$(grep -oE '"(PolyQF|Challenge|Solution)\.[A-Za-z0-9_.]+"' comparator.json | tr -d '"' | grep -v '\.lean$' | sort -u)
tmp=$(mktemp -d)
{
  echo "import RequestProject"
  echo "import Challenge"
  echo "import Solution"
  for n in $names; do
    echo "#print axioms $n"
  done
} > "$tmp/AxiomCheck.lean"

out=$(lake env lean "$tmp/AxiomCheck.lean" 2>&1)
echo "$out"
if echo "$out" | grep -qE "error"; then
  echo "FAIL: could not check all names."
  status=1
elif echo "$out" | grep -vE "propext|Classical\.choice|Quot\.sound|does not depend on any axioms" | grep -q "depends on axioms"; then
  echo "FAIL: a result depends on a non-standard axiom."
  status=1
else
  echo "OK: only propext, Classical.choice and Quot.sound are used."
fi
rm -rf "$tmp"
echo

if [ "$status" -eq 0 ]; then
  echo "ALL CHECKS PASSED"
else
  echo "SOME CHECKS FAILED"
fi
exit "$status"
