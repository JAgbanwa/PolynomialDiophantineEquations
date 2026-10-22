#!/usr/bin/env bash
# Verify the paper statements with the comparator bundled in Lean 4.35.0.
# Run `lake exe cache get` first. A working Linux bubblewrap sandbox is required.
# Every stage is mandatory; no failure is converted to a skipped success.
set -euo pipefail
cd "$(dirname "$0")"

if (( $# != 0 )); then
  printf 'Usage: bash verify.sh\n' >&2
  exit 64
fi

printf '==> [1/3] checking project files, statement inventory, and proof sources\n'
python3 scripts/check_project.py
python3 scripts/check_metadata.py
if [[ "$(tr -d '\r\n' < lean-toolchain)" != 'leanprover/lean4:v4.35.0' ]]; then
  printf 'error: this verification setup requires the committed Lean 4.35.0 toolchain\n' >&2
  exit 1
fi
lake --version
if ! command -v "${COMPARATOR_BWRAP:-bwrap}" >/dev/null; then
  printf 'error: bubblewrap is required by lake comparator; install the Linux bubblewrap package\n' >&2
  exit 1
fi

# Comparator builds and exports Challenge and Solution in its real sandbox,
# compares all listed statements and their definitions, checks the axiom
# allowlist, and replays the exported solution through the Lean kernel.
# Run it before compiling project code outside that sandbox.
printf '==> [2/3] running the Lean comparator with its sandbox enabled\n'
lake comparator --config comparator.json

printf '==> [3/3] building every advertised project target\n'
lake build RequestProject Challenge Solution

printf '==> all checks passed\n'
