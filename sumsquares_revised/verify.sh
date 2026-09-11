#!/usr/bin/env bash
# Verification script for the formalization of
#   "On the polynomial values represented by quadratic forms" (B. Grechuk, J. Agbanwa).
#
# The whole formalization lives in the single file `RequestProject.lean`.
#
# It (1) builds the project and checks that it elaborates without errors *or warnings*,
# (2) checks the source for `sorry`, `admit`, user-declared `axiom`s and `@[implemented_by]`,
# and (3) prints the axiom dependencies of every name listed in `comparator.json`.

set -uo pipefail

cd "$(dirname "$0")"

status=0

echo "== 1/3  Building =="
if ! lake build; then
  echo "FAIL: lake build failed."
  exit 1
fi
echo "OK: build succeeded."

diagnostics=$(lake env lean RequestProject.lean 2>&1)
if [ -n "$diagnostics" ]; then
  echo "$diagnostics"
  echo "FAIL: the file produced diagnostics (errors or warnings)."
  status=1
else
  echo "OK: RequestProject.lean elaborates with no errors and no warnings."
fi
echo

echo "== 2/3  Scanning the source =="
pattern='\bsorry\b|\badmit\b|^[[:space:]]*axiom[[:space:]]|@\[implemented_by'
if grep -nE "$pattern" RequestProject.lean; then
  echo "FAIL: forbidden constructs found above."
  status=1
else
  echo "OK: no sorry / admit / axiom / @[implemented_by] in the source."
fi
echo

echo "== 3/3  Checking axiom dependencies =="
names=$(grep -oE '"(PolyQF|Challenge|Solution)\.[A-Za-z0-9_.]+"' comparator.json | tr -d '"')
tmp=$(mktemp -d)
{
  echo "import RequestProject"
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
