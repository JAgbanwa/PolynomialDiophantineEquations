# Lean formalisation: "On the polynomial values represented by binary quadratic forms"

Lean 4 source for the paper by B. Grechuk and J. Agbanwa (revision R1).
The intended toolchain is `leanprover/lean4:v4.28.0`, with Mathlib `v4.28.0`.

## Verification status

**The published revision is not yet a reproducibly verified project.** An audit on
22 October 2026 inspected commit
[`f7b8950b458b67621b378c3e496b6a2bb9f22b3d`](https://github.com/JAgbanwa/PolynomialDiophantineEquations/tree/f7b8950b458b67621b378c3e496b6a2bb9f22b3d/sumsquares_revision).
That snapshot has these packaging problems:

- `Challenge.lean` is missing, although the configuration expects it.
- The source directory is named `RequestProject ` **with a trailing space**.
  `Solution.lean` imports `RequestProject.Main`, which requires
  `RequestProject/Main.lean` without that space.
- Neither `lean-toolchain` nor `lake-manifest.json` is committed in this folder.
  Lake may generate these locally when resolving dependencies; that does not make
  them part of the published snapshot.
- The existing GitHub Actions workflow builds **`sumsquares_revised`**, a different
  folder. Its green checks do not establish a successful build of
  **`sumsquares_revision`**.

The instructions below explain how to obtain and record an actual successful
build **after the missing files and source-path problem are repaired**. At the
audited snapshot, the preflight check intentionally stops. An example success
message below is an acceptance criterion, not a claim that this snapshot passed.

### Observed checks on 22 October 2026

The audit installed Lean 4.28.0 and resolved Mathlib to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

| Check | Observed result |
| --- | --- |
| `lake +leanprover/lean4:v4.28.0 build RequestProject Challenge Solution` in the published layout | **Failed**, exit code 1: Lake cannot find the `RequestProject` directory. |
| Direct check of the unchanged `RequestProject /Main.lean` | **Passed**, exit code 0. |
| `lake build RequestProject Solution` in a temporary directory with the source path corrected and both Lean source files copied byte-for-byte | **Passed**, exit code 0: `Build completed successfully (8029 jobs).` This was a two-target diagnostic, excluding the absent `Challenge`. |
| `#print axioms` for all 42 `Paper.*` declarations after the two-target build | **Passed**: every reported axiom belongs to `{propext, Classical.choice, Quot.sound}`; no `sorryAx` was reported. |
| Independent challenge comparison / official comparator | **Not performed**: the published challenge is absent. |

Thus the proof development and its solution wrappers compile with the intended
dependencies after correcting the path in a temporary copy. This does not certify
the complete published package or its agreement with an independent challenge.
The reproducible proof-only diagnostic appears after the full-project instructions.

## Mathematical scope

`Solution.lean` contains 42 theorem statements matching the 42 names in
`comparator.json`. They include the tangent criterion, Propositions 2.2, 4.1 and
4.2, Corollaries 3.1 and 3.2, Proposition 4.3, and both directions of the
degenerate-case criterion. This is a source inventory; successful compilation
and comparator verification are separate requirements.

The algorithm results prove the correctness of the conclusions of Algorithms
2.1 and 4.1 **when suitable seed data and the stated hypotheses are supplied**.
They also cover reduction to quadratic auxiliary equations and the linear-case
seed tests. They do not implement the full seed searches or general quadratic
equation decision procedures, or assert termination for arbitrary inputs.

The development defines `PolyQF.S2` using **positive** integers. It excludes the
informal introductory discussion, the list of open equations in Table 1, and
the footnote claim that `u = 50` is the smallest successful positive seed for
`f = -4`. The example proofs use the sufficient seed `u = 162`.

## Intended project layout

| File | Purpose and status at the audited snapshot |
| --- | --- |
| `RequestProject/Main.lean` | Main mathematical development. Currently uploaded under the incorrectly named directory `RequestProject `. |
| `Challenge.lean` | **Missing.** Must independently state the advertised results as `theorem ... := by sorry`, importing Mathlib and including the required definitions. It must not import the solution or proof development. |
| `Solution.lean` | Proof interface in namespace `Paper`, using the development in namespace `PolyQF`. |
| `lean-toolchain` | **Missing from Git.** Must pin `leanprover/lean4:v4.28.0` for this version. |
| `lakefile.toml` | Package configuration and three build targets: `RequestProject`, `Challenge`, `Solution`. |
| `lake-manifest.json` | **Missing from Git.** Commit the resolved dependency revisions for the final reproducible snapshot. |
| `comparator.json` | Configuration for the official [comparator](https://github.com/leanprover/comparator). |
| `formalization.yaml` | Existing metadata requires conversion to the actual v0.4 schema; see below. |
| `verify.sh` | Builds targets, checks proof sources, runs the diagnostic pre-check, and then requires the real comparator. Invoke with `bash`, because its executable bit is not set. |
| `scripts/CheckComparator.lean` | Diagnostic check of statements, challenge-local definitions, and axiom dependencies. It does not replace the comparator. |

## Step-by-step build instructions

Use a Bash terminal on Linux or macOS. On Windows, the same commands can be run
inside an Ubuntu WSL terminal. The standalone comparator requires a compatible
Linux environment. The first dependency download needs an internet connection
and substantial free disk space.

### 1. Install prerequisites and Elan

Install Git and curl using your operating system's package manager. For Ubuntu:

```bash
sudo apt update
sudo apt install git curl
```

If Elan is not already installed, use the official installer. These commands
install the version manager without selecting an unrelated default Lean release:

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
source "$HOME/.elan/env"
elan --version
```

See the [official Lean installation guide](https://lean-lang.org/install/manual/)
for platform-specific alternatives. If `lake` is not found, reopen the terminal
or repeat `source "$HOME/.elan/env"`.

### 2. Clone the repository and enter the correct folder

Run this in a directory where a new checkout should be created:

```bash
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git
cd PolynomialDiophantineEquations
git rev-parse HEAD
cd sumsquares_revision
```

Keep the full commit hash printed by `git rev-parse HEAD`. For a final paper
snapshot, check out the exact commit cited in the paper before entering the
project folder. Do not substitute `sumsquares_revised` when testing this revision.

### 3. Check that the required project files are present

Run the whole block from `sumsquares_revision`:

```bash
(
  set -eu
  for file in lean-toolchain lakefile.toml lake-manifest.json \
      RequestProject/Main.lean Challenge.lean Solution.lean \
      comparator.json formalization.yaml verify.sh scripts/CheckComparator.lean
  do
    if [ ! -f "$file" ]; then
      printf 'Missing required file: %s\n' "$file" >&2
      exit 1
    fi
  done
  if [ -d 'RequestProject ' ]; then
    printf 'Unexpected trailing space in directory: RequestProject \n' >&2
    exit 1
  fi
  printf 'Project-file preflight passed.\n'
)
```

**Stop if this check fails.** In particular, do not work around a missing
`Challenge.lean` by removing it from the build targets: the challenge is part of
the referee's requested verification. The maintainer must restore it and correct
the source directory name in the published project.

### 4. Install and verify the pinned toolchain

For this revision, `lean-toolchain` must contain
`leanprover/lean4:v4.28.0`:

```bash
cat lean-toolchain
elan toolchain install leanprover/lean4:v4.28.0
lake env lean --version
lake --version
```

The Lean version must report **4.28.0**. Do not run `elan default stable` as a
substitute for the project pin. Updating Lean is a separate change that also
requires a compatible Mathlib revision and another complete verification run.

### 5. Download the matching Mathlib build cache

```bash
lake exe cache get
```

Wait for this command to finish successfully. It downloads dependency build
artefacts; it is not a verification of this project's theorems. For a published
snapshot, preserve the committed `lake-manifest.json` instead of deleting it or
updating dependencies to newer versions.

### 6. Build all three targets and preserve the result

Run this complete block. The Bash `pipefail` setting ensures that a failed
`lake build` is not concealed by a successful `tee` command:

```bash
(
  set -euo pipefail
  {
    date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
    git rev-parse HEAD
    git status --short
    lake env lean --version
    lake --version
    git -C .lake/packages/mathlib rev-parse HEAD
  } | tee build-environment.log

  lake build RequestProject Challenge Solution 2>&1 | tee build.log
  printf 'Build exit code: 0\n' | tee -a build.log
)
```

A successful run ends with Lake's message beginning
`Build completed successfully` and the recorded line `Build exit code: 0`.
The environment log also records local changes; use a clean source checkout
when certifying an immutable paper snapshot. The number of build jobs varies.
If there is an error or a nonzero exit code,
the build has **not** completed successfully; preserve the error log for repair.

Deliberate `sorry` warnings in **`Challenge.lean`** are expected: it specifies
the claims to be checked. Such placeholders must not occur in the proof
development or `Solution.lean`, or be dependencies of their proofs. A successful
build alone does not establish this stronger condition.

For an additional fresh build of the project's own targets, after a successful
initial run:

```bash
lake clean
lake build RequestProject Challenge Solution
```

### 7. Run the diagnostic pre-check and the real comparator

After the build succeeds, the optional diagnostic check is:

```bash
lake env lean --run scripts/CheckComparator.lean
```

It compares the listed statements, checks reachable challenge-local definitions,
and inspects axiom dependencies. It does not perform the official comparator's
complete exported-environment checks, kernel replay, or sandboxed workflow.

For the standalone comparator used with this Lean 4.28 project, install a
compatible comparator binary, `landrun`, and a `lean4export` version compatible
with Lean 4.28.0, following the [upstream instructions](https://github.com/leanprover/comparator).
Check that the two helper programs are on `PATH`, then supply the actual
comparator executable path:

```bash
command -v landrun
command -v lean4export
read -r -p 'Absolute path to the comparator executable: ' COMPARATOR
(
  set -euo pipefail
  test -x "$COMPARATOR"
  COMPARATOR="$COMPARATOR" bash verify.sh 2>&1 | tee verification.log
)
```

The script must finish with `==> all checks passed` and exit code zero. A missing
comparator is a failure, not a skipped success. These are the project's commands;
follow upstream's environment and sandbox requirements for an authoritative
comparator run. For independent verification, use a fresh checkout and follow
upstream's trusted-challenge procedure before compiling the proposed solution.
No successful comparator run is claimed for the audited snapshot.

Lean 4.35.0 incorporates comparator functionality as `lake comparator` / `lake check`.
That is relevant to a future toolchain upgrade; it does not make those commands
available in this project's intended Lean 4.28.0 toolchain.

## Reproduce the successful proof-only diagnostic

This separate diagnostic uses the exact audited source commit. It checks the
existing proofs while leaving the checkout unchanged. It deliberately builds
only `RequestProject` and `Solution`; it is **not** a substitute for restoring
`Challenge.lean` and completing the full verification above.

After installing Elan as in Step 1, run the following from anywhere inside the
cloned repository. The temporary directory is printed so its logs can be kept.

```bash
(
  set -euo pipefail
  PAPER_REPO_ROOT=$(git rev-parse --show-toplevel)
  AUDITED_COMMIT=f7b8950b458b67621b378c3e496b6a2bb9f22b3d
  PROOF_AUDIT_DIR=$(mktemp -d)
  printf 'Proof diagnostic directory: %s\n' "$PROOF_AUDIT_DIR"
  mkdir -p "$PROOF_AUDIT_DIR/RequestProject"

  git -C "$PAPER_REPO_ROOT" show \
    "$AUDITED_COMMIT:sumsquares_revision/RequestProject /Main.lean" \
    > "$PROOF_AUDIT_DIR/RequestProject/Main.lean"
  for file in Solution.lean lakefile.toml comparator.json; do
    git -C "$PAPER_REPO_ROOT" show \
      "$AUDITED_COMMIT:sumsquares_revision/$file" > "$PROOF_AUDIT_DIR/$file"
  done
  printf 'leanprover/lean4:v4.28.0\n' > "$PROOF_AUDIT_DIR/lean-toolchain"

  cd "$PROOF_AUDIT_DIR"
  elan toolchain install leanprover/lean4:v4.28.0
  lake exe cache get
  lake env lean --version
  git -C .lake/packages/mathlib rev-parse HEAD
  lake build RequestProject Solution 2>&1 | tee proof-build.log
  printf 'Proof-only build exit code: 0\n' | tee -a proof-build.log
)
```

The audit obtained `Build completed successfully (8029 jobs).` from this
two-target build; the job count can differ with the cache state. The source files
checked had these SHA-256 hashes:

| Source | SHA-256 |
| --- | --- |
| `Main.lean` | `02d13e6ad8cbf2800c676540d5d8ee729f3606951dac3a674bfa20dbb063583b` |
| `Solution.lean` | `b2a3cf72916534b3b56b7f36ce33cf6a0b041646aa2ad3142787d85ac77ad7b4` |

To reproduce the axiom diagnostic, change into the printed temporary directory.
This additional command uses Python 3's standard library to generate the 42
inspection commands directly from the comparator configuration:

```bash
python3 - <<'PY'
import json
from pathlib import Path
names = json.loads(Path("comparator.json").read_text())["theorem_names"]
Path("AxiomAudit.lean").write_text(
    "import Solution\n\n"
    + "\n".join("#print axioms " + name for name in names)
    + "\n"
)
PY
set -o pipefail
lake env lean AxiomAudit.lean 2>&1 | tee axioms.log
```

Inspect all 42 outputs: only `propext`, `Classical.choice`, and `Quot.sound`
should occur. This diagnostic checks axiom dependencies, not independent
statement matching or the official comparator's other checks.

## Remaining referee requirements

In addition to obtaining a successful build and comparator run:

1. Restore an independent `Challenge.lean` with the same 42 theorem statements
   and the required definitions. Review its statements against the paper;
   agreement between two files is not by itself proof of fidelity to the paper.
2. Convert `formalization.yaml` using the official
   [v0.4 template and schema](https://github.com/mathlib-initiative/formalization.yaml).
   The present file lacks the required top-level sections `project`, `sources`,
   `automation`, and `review`. The default version-dispatcher schema expects
   `version: "v0.4"`, not `version: "0.4"`.
3. Make the CI workflow test `sumsquares_revision` and its actual comparator
   setup. Do not treat the existing older-folder checks as evidence for this one.
4. Select one immutable, verified project commit and use it for the paper's
   project link, proof-file link, and this README's citation.

The source comments now distinguish [11, Proposition 5.4] in the quadratic
sum-of-squares seed argument from [11, Proposition 3.14] in the general-form
argument. Some equation-number comments still need alignment with the final
manuscript. The optional Lean 4.35.0 upgrade is separate from these mandatory
corrections.

## Citing this formalisation

The audit snapshot named above is **not** a verified final publication snapshot.
After repairs and verification, record the full commit hash and use that same
hash in both links in footnote b and in this section. The project and proof file
must belong to that one snapshot, under `sumsquares_revision` with the corrected
`RequestProject/Main.lean` path. Record the tested commit alongside the build and
comparator logs. A moving `main` URL is not an immutable citation.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:

- Tag @Aristotle-Harmonic on GitHub PRs/issues.
- Add as co-author to commits that include Aristotle's work:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
