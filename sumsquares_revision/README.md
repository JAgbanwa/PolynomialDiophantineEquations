# Lean formalisation: “On the polynomial values represented by binary quadratic forms”

Lean formalisation of the paper by Bogdan Grechuk and Jamal Agbanwa, IJNT manuscript
IJNT-D-26-00150. This project uses **Lean 4.35.0** and **Mathlib v4.35.0**, with all
resolved dependency revisions committed in `lake-manifest.json`.

## Verification and paper snapshot

This repair restores the independent challenge and complete verification setup.
The full Lean 4.35.0 build passed on 22 October 2026, ending with
`Build completed successfully (9052 jobs).` The official comparator is being
checked in CI; its completed run and the immutable paper snapshot will be
recorded here before the revision is finalized. An installed verifier is not itself evidence
of a successful verification run.

The project link and proof-file link in the paper must refer to the **same
immutable commit** in `sumsquares_revision`. The older directory
`sumsquares_revised` is a separate development. This README, the challenge, the
solution, the metadata, and the dependency pins belong to this project together.

## What is formalised

`Challenge.lean` independently states **42 theorems** in namespace `Paper`. It
imports only Mathlib and supplies four explicit definitions: positive sums of
two squares (`S2`), the Taylor quotient (`Du`), the binary quadratic form (`bqf`),
and the admissible degree pairs (`AdmissibleDegrees`). Each theorem has the
deliberate placeholder `by sorry` required for the comparison interface.

`Solution.lean` proves the same 42 statements through
`RequestProject/Main.lean`. Neither proof file imports the challenge. The
comparator checks the statements and their dependencies, restricts the solution
axioms to `propext`, `Quot.sound`, and `Classical.choice`, and replays the exported
solution in the Lean kernel. `sorryAx` is not permitted for the solution.

| Manuscript content | Representative declarations in `Paper` |
| --- | --- |
| Taylor quotient, tangent identity, and positive sums of two squares | `taylor_identity`, `Du_unique`, `natDegree_Du_le`, `tangent_identity`, `S2_iff_prime_exponents`, `property_star` |
| Sum-of-two-squares criteria | `proposition_2_1`, `proposition_2_2` |
| Algorithm 2.1, quadratic reduction and linear seed test | `aux_equation_quadratic`, `algorithm_2_1_step2`, `algorithm_2_1`, `algorithm_2_1_linear_seed_test` |
| Applications in Section 3 | `corollary_3_1`, `corollary_3_2`, `remark_x6_plus_3`, and the supporting identities and explicit equations |
| General binary quadratic forms | `proposition_4_1_recovery`, `proposition_4_1`, `proposition_4_2` |
| Algorithm 4.1 and its linear seed test | `algorithm_4_1_step2`, `algorithm_4_1`, `algorithm_4_1_linear_seed_test` |
| Explicit polynomial families and examples | `proposition_4_3_families`, `proposition_4_3`, `proposition_4_3_data`, `non_multiplicative_example`, `four_sum_two_squares_remark` |
| Degenerate forms, including both directions of the criterion | `degenerate_parametrisation`, `degenerate_form_eq`, `degenerate_infinite_iff` |
| Comparison of the two constructions | `comparison_with_section_2` |

The full 42-name inventory is in `comparator.json`; the statement-to-paper map is
in `formalization.yaml`. Numbering follows the supplied final manuscript. The
referee's references to the earlier Propositions **2.2 and 2.3** correspond to
**2.1 and 2.2** in that manuscript. The general Propositions **4.1 and 4.2** keep
their numbers.

### Scope of the claims

The algorithm theorems prove **conditional correctness when suitable seed data
and the stated hypotheses are supplied**. The quadratic reductions and the
linear-case seed tests are included. General seed searches, executable general
quadratic-equation solvers, and termination for arbitrary inputs are not claimed.

`S2` consists of positive integers, as in the paper. The infinitude conclusion
for the degenerate case concerns solution triples; it can hold with a fixed
`x`. The introductory survey, Table 1 of open problems, and the footnote claim
that `u = 50` is the smallest successful positive seed for `f = -4` are outside
the formalised scope. The sufficient seed `u = 162` used in the proof is checked.

The proof of the auxiliary sum-of-two-squares criterion corresponds to the
paper's citation **[11, Proposition 5.4]**. The general criterion retains the
correct citation **[11, Proposition 3.14]**. The Lean development proves the
needed infinitude statements internally using a Pell-orbit argument.

## Project files

| File | Purpose |
| --- | --- |
| `RequestProject/Main.lean` | Mathematical proofs in namespace `PolyQF` |
| `Challenge.lean` | Independent theorem statements with deliberate placeholders |
| `Solution.lean` | Completed proof interface in namespace `Paper` |
| `lean-toolchain` | Exact Lean version |
| `lakefile.toml`, `lake-manifest.json` | Build targets and pinned dependencies |
| `comparator.json` | Configuration for the official Lean comparator |
| `formalization.yaml` | Metadata in the official v0.4 format |
| `verify.sh` | Required source checks, metadata validation, real comparator, and full build |
| `scripts/check_project.py` | Structural preflight and source-placeholder checks |
| `scripts/check_metadata.py` | Validation against the vendored official v0.4 schema |
| `scripts/CheckComparator.lean` | Optional diagnostic; does not replace the official comparator |
| `../.github/workflows/sumsquares-revision-ci.yml` | CI verification of this directory |

## Practical instructions: obtain a successful build and verification

Use a **Bash terminal on Linux** for the complete procedure. The official Lean
4.35 comparator requires a working `bubblewrap` sandbox. An Ubuntu environment
with permission to create the required namespaces and mount its isolated `/proc`
is suitable. Some containers and hosted notebooks prohibit those operations;
in that case use the repository's GitHub Actions workflow or another suitable
Linux machine. Ordinary compilation can also run on the other platforms Lean
supports, but it does not replace the comparator check.

The first download needs an internet connection and several gigabytes of disk
space. Run the numbered steps in order. A failed command must be resolved before
claiming that verification succeeded.

### 1. Install system prerequisites and Elan

For Ubuntu:

```bash
sudo apt-get update
sudo apt-get install -y git curl bubblewrap python3 python3-venv
```

If Elan is not installed, obtain the official installer and install the version
manager without choosing an unrelated default Lean version:

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
source "$HOME/.elan/env"
elan --version
```

See the [official Lean installation guide](https://lean-lang.org/install/manual/)
for installation details. If `lake` is not found, reopen the terminal or run
`source "$HOME/.elan/env"` again.

### 2. Clone the repository and select this revision

Run in a directory where a new checkout can be created:

```bash
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git
cd PolynomialDiophantineEquations
git switch fix/sumsquares-referee-lean
git rev-parse HEAD
cd sumsquares_revision
```

The final paper citation will pin an immutable commit after verification. Keep
the full hash printed above in the meantime. All subsequent commands run from
`sumsquares_revision`.

### 3. Install the pinned metadata validator

Create the virtual environment outside the source tree:

```bash
python3 -m venv ../sumsquares-verification-venv
source ../sumsquares-verification-venv/bin/activate
python3 -m pip install -r scripts/requirements.txt
python3 scripts/check_project.py
python3 scripts/check_metadata.py
```

Expected preflight messages include:

```text
OK: 42 named statements in each interface; proof sources contain no placeholders or extra axioms.
OK: formalization.yaml conforms to the pinned v0.4 schema.
```

The schema is an unmodified, pinned copy of the
[official v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json).
Its source and license are recorded in `scripts/schema/README.md`.

### 4. Install Lean 4.35.0 and download the matching dependency cache

```bash
cat lean-toolchain
elan toolchain install leanprover/lean4:v4.35.0
lean --version
lake --version
lake exe cache get
```

`lean-toolchain` must read `leanprover/lean4:v4.35.0`, and the Lean version must
report **4.35.0**. Wait for the cache command to finish successfully. The cache
contains dependency build artifacts; it does not certify this project's proofs.
Preserve the committed manifest. Do not run `lake update` or substitute newer
dependencies when reproducing the paper snapshot.

### 5. Check that the comparator sandbox works

```bash
bwrap --version
bwrap --unshare-all --ro-bind / / --proc /proc --dev /dev -- /bin/true
```

The second command must finish with exit code zero. Errors such as
`Operation not permitted` mean that this environment cannot run the required
sandbox. Use a suitable Linux host or GitHub Actions; do not bypass the sandbox
or describe an axiom-only diagnostic as a comparator pass.

### 6. Run the complete verification and save the evidence

Run the entire block below. Bash `pipefail` preserves a failing verifier's exit
status even though the output is also written by `tee`.

```bash
(
  set -euo pipefail
  {
    date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
    git rev-parse HEAD
    git status --short --untracked-files=no
    lean --version
    lake --version
    git -C .lake/packages/mathlib rev-parse HEAD
  } | tee build-environment.log
  git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
  bash verify.sh 2>&1 | tee verification.log
  printf 'Verification exit code: 0\n' | tee -a verification.log
)
```

`verify.sh` first checks the source inventory and metadata, then runs the real
**`lake comparator --config comparator.json`**, then explicitly builds every
advertised target using **`lake build RequestProject Challenge Solution`**.
Lean 4.35 supplies the comparator and matching exporter; no standalone
`COMPARATOR` path, `landrun`, or separately installed `lean4export` is needed.

A successful run must contain the comparator's successful conclusion, Lake's
message beginning **`Build completed successfully`**, the final verifier line
**`==> all checks passed`**, and **`Verification exit code: 0`**. The number of
build jobs varies. If the block returns a nonzero status, verification has failed.

Warnings about deliberate `sorry` proofs in **`Challenge.lean`** are expected.
They are specification placeholders and are never imported by the solution.
The comparator must reject a solution whose proof depends on `sorryAx` or any
axiom outside the three permitted ones.

### 7. Reproduce only the explicit build, if needed

After the complete verification, the compilation command can be repeated alone:

```bash
(
  set -euo pipefail
  lake build RequestProject Challenge Solution 2>&1 | tee build.log
  printf 'Build exit code: 0\n' | tee -a build.log
)
```

This is the direct way to record **“Build completes successfully.”** It checks
all three targets. Its success does not independently replace the comparator.

For a fresh rebuild of this package while retaining the dependency cache:

```bash
lake clean RequestProject
lake build RequestProject Challenge Solution
```

The optional local diagnostic is:

```bash
lake env lean --run scripts/CheckComparator.lean
```

It compares the interfaces and examines axiom dependencies. The official
comparator also exports, compares and kernel-checks in its sandbox; the diagnostic
is useful for debugging but is not an equivalent verification procedure.

## Verification in GitHub Actions

Open the repository's **Actions** tab and choose **Sumsquares revision
verification**. Select the run for the cited commit and inspect the step
**Run the real comparator and full project build**. The workflow performs the
same mandatory verifier and uploads the environment, sandbox and verification
logs as a run artifact. A successful workflow for the older
`sumsquares_revised` directory does not verify this package.

The new workflow runs on pull requests and pushes affecting this project, and
also supports manual dispatch. Its green result is meaningful only for the
commit and working directory recorded in the run. Retain the logs with the
paper's final submitted revision.

## Provenance

The original formal proof development was assisted by
[Aristotle (Harmonic)](https://aristotle.harmonic.fun). The revision audit,
statement interface, packaging repairs and reproducibility checks were assisted
by ChatGPT. `formalization.yaml` records the scope, sources, automation, review
status and known differences between the paper's proofs and the Lean proofs.
