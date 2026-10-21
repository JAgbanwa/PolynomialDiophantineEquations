#!/usr/bin/env bash
# Verification script for the Lean formalisation of
#   B. Grechuk and J. Agbanwa, "On the polynomial values represented by binary quadratic forms".
#
# Steps:
#   1. build the development (RequestProject/Main.lean), Challenge.lean and Solution.lean;
#   2. check that RequestProject/Main.lean and Solution.lean contain no `sorry`;
#   (pre-check) scripts/CheckComparator.lean re-checks the comparator conditions in Lean;
#   3. run the comparator (https://github.com/leanprover/comparator) on comparator.json.
#      The comparator checks that every theorem listed in comparator.json is stated
#      identically in Challenge.lean and Solution.lean (including the definitions the
#      statements use), that Solution.lean proves it, and that the proofs use only the
#      permitted axioms.  It needs `landrun` and `lean4export` on PATH.
#
# Set COMPARATOR to the comparator binary, e.g.
#   COMPARATOR=~/comparator/.lake/build/bin/comparator ./verify.sh
# Step 3 is mandatory: the script fails if the comparator is not available.
set -euo pipefail
cd "$(dirname "$0")"

echo "==> [1/3] lake build"
lake build RequestProject Challenge Solution

echo "==> [2/3] checking for sorry in the development and the solution"
if grep -nwE 'sorry|admit' RequestProject/Main.lean Solution.lean | grep -v '^\S*:[0-9]*:.*`sorry`'; then
  echo "error: sorry/admit found" >&2
  exit 1
fi
if grep -nE '^\s*(axiom|@\[implemented_by)' RequestProject/Main.lean Solution.lean Challenge.lean; then
  echo "error: axiom or implemented_by declaration found" >&2
  exit 1
fi

echo "==> offline pre-check of the comparator conditions (scripts/CheckComparator.lean)"
lake env lean --run scripts/CheckComparator.lean

echo "==> [3/3] running the comparator on comparator.json"
COMPARATOR="${COMPARATOR:-$(command -v comparator || true)}"
if [ -z "$COMPARATOR" ] || [ ! -x "$COMPARATOR" ]; then
  echo "error: comparator binary not found; set COMPARATOR=/path/to/comparator" >&2
  echo "       (an offline pre-check is available: lake env lean --run scripts/CheckComparator.lean)" >&2
  exit 1
fi
for tool in landrun lean4export; do
  command -v "$tool" >/dev/null || { echo "error: $tool not found on PATH (required by the comparator)" >&2; exit 1; }
done
lake env "$COMPARATOR" comparator.json

echo "==> all checks passed"
