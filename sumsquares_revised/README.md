# On the polynomial values represented by quadratic forms — Lean formalization

Lean 4 formalization of the paper

> **On the polynomial values represented by quadratic forms**
> Bogdan Grechuk and Jamal Agbanwa [\[1\]](https://arxiv.org/pdf/2607.06627)

The development proves, with no `sorry` and no added `axiom`, that `x⁶ − 4` is a sum of
two squares for infinitely many integers `x`, and hence that the Diophantine equation
`y² + x³y + z² + 1 = 0` has infinitely many integer solutions (Corollary 3.1), together
with the four further length-9 equations of Corollary 3.2, the general theory of
Section 4 (Propositions 4.1, 4.2, 4.4, Algorithms 2.4 and 4.3, non-multiplicativity of
`2y² + yz + 2z²`, and the degenerate case `B² − 4AC = 0`), and the supporting machinery
(property (*) of the sums of two squares, Gauss's theorem on generalised Pell equations
and a residue-controlled refinement of it).

## Versions

The project pins its dependencies exactly, so it will keep compiling as Lean and Mathlib
evolve:

| Component | Version |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.28.0` (see `lean-toolchain`) |
| Mathlib | tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (see `lakefile.toml` and `lake-manifest.json`) |

`lake-manifest.json` is committed, so `lake build` reconstructs exactly the dependency
revisions against which the proofs were checked.

## Layout

| Path | Contents |
| --- | --- |
| `RequestProject.lean`, `RequestProject/Main.lean` | the proof development: all definitions, lemmas and theorems |
| `Challenge.lean` | the small, human-auditable statement surface: the paper's main results, stated using Mathlib alone |
| `Solution.lean` | the same declarations, with the same names and types, proved from the development |
| `comparator.json` | the [comparator](https://github.com/leanprover/comparator) configuration naming the compared declarations and the permitted axioms |
| `formalization.yaml` | project metadata in the `mathlib-initiative` `formalization.yaml` v0.4 format |
| `verify.sh` | independent verification of `Challenge.lean` against `Solution.lean` with `comparator` |

`Challenge.lean` contains one deliberate `sorry` per advertised statement: by the
comparator convention that file advertises statements only, and `Solution.lean` supplies
the proofs. There is no `sorry` anywhere else in the project, and no `axiom` declaration
at all.

## Building

```sh
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build           # builds RequestProject, Challenge and Solution
```

## Independent verification with `comparator`

```sh
./verify.sh              # add COMPARATOR_SKIP_CACHE=1 if Mathlib is already built
```

The script fetches and builds [`comparator`](https://github.com/leanprover/comparator)
and [`lean4export`](https://github.com/leanprover/lean4export) at the tag matching
`lean-toolchain`, together with the `landrun` sandbox they use, and then runs the
comparator on `comparator.json`. Comparator rebuilds `Challenge` and `Solution` in a
sandbox, checks that the sixteen compared declarations have exactly the statements advertised
in `Challenge.lean`, checks that their axiom closure lies inside the permitted set, and
re-checks the proofs with the Lean kernel; it prints `Your solution is okay!` on success.
Only the Lean kernel, Mathlib, `Challenge.lean` and comparator itself have to be trusted.
Setting `"enable_nanoda": true` in `comparator.json` additionally re-checks the proofs
with the independent `nanoda` kernel, which must then be on `PATH`.

## Axioms

Every theorem in `RequestProject/Main.lean` and `Solution.lean` depends only on the three
standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. In particular no
proof uses `native_decide`, so `Lean.ofReduceBool` does not appear: the four
non-squareness facts needed in Section 3 (`a = 17006096, 8320, 208, 80`) are proved from
the bounds given in the paper (for instance `4123² < 17006096 < 4124²`) by the elementary
lemma `SumSquaresPaper.not_isSquare_of_between` together with `norm_num`.

You can check this yourself:

```sh
echo 'import Solution
#print axioms PolynomialValuesQuadraticForms.equation_2_infinite' > /tmp/axioms.lean
lake env lean /tmp/axioms.lean
```

## Proof organization

The formalized statements are the paper's statements. The implementation records
proof-engineering details in the module docstring of `RequestProject/Main.lean` and in
`formalization.yaml`:

* **Proposition 4.2** uses the revised manuscript's residue-controlled Pell argument
  (`genPell_infinite_cong`). The Lean statement also records that the non-degeneracy
  assumption `Δ ≠ 0` is not needed for Proposition 4.2 itself.
* **Proposition 4.4** is verified directly from the explicit polynomial families given in
  the paper (by `ring`), rather than by re-running the tangent construction.

In addition, Gauss's theorem on generalised Pell equations, quoted in the paper from
[11, Proposition 5.4], is proved from scratch here rather than assumed.

## Licence

No `LICENSE` file has been added: the choice of licence is for the authors. A registry
submission expects a licence file at the repository root, and `project.license` in
`formalization.yaml` should then be updated to match it.

## Credits

The Lean proofs were produced with [Aristotle](https://aristotle.harmonic.fun) (Harmonic).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## Reproducing the Lean build locally

The project is pinned to **Lean 4.28.0** and a fixed Mathlib revision through `lean-toolchain` and `lake-manifest.json`. The following instructions reproduce the successful build on macOS using Terminal. They also work on most Linux systems.

### 1. Prerequisites

Check that Git and curl are installed:

```bash
git --version
curl --version
```

On macOS, running `git --version` may prompt you to install the Xcode Command Line Tools. Approve that installation if necessary.

### 2. Install Elan

Elan manages Lean installations and automatically selects the version specified by the project’s `lean-toolchain` file.

Check whether Elan is already installed:

```bash
elan --version
```

If the command is not found, install Elan with:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Choose the default installation option when prompted. Then activate Elan in the current Terminal session:

```bash
source ~/.elan/env
```

Confirm the installation:

```bash
elan --version
```

If `lake` is still not found after installation, either run `source ~/.elan/env` again or close and reopen Terminal.

### 3. Clone a fresh copy of the repository

A fresh clone is recommended because older copies of the repository contained directory names with literal trailing spaces.

For example:

```bash
cd ~/Documents
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-build-test
cd PolynomialDiophantineEquations-build-test/sumsquares_revised
```

The correct directory name is:

```text
sumsquares_revised
```

There is no trailing space after `revised`.

Confirm the current location and project contents:

```bash
pwd
ls
```

The directory should contain at least:

```text
Challenge.lean
README.md
RequestProject/
RequestProject.lean
Solution.lean
comparator.json
lake-manifest.json
lakefile.toml
lean-toolchain
verify.sh
```

The relevant Lean module layout is:

```text
sumsquares_revised/
├── RequestProject.lean
└── RequestProject/
    └── Main.lean
```

This path is important because:

```lean
import RequestProject.Main
```

corresponds to the filesystem path:

```text
RequestProject/Main.lean
```

### 4. Record the exact repository revision

For reproducibility, record the commit being built:

```bash
git branch --show-current
git rev-parse HEAD
git status --short
```

For a fresh clone, the branch should normally be `main`, and `git status --short` should produce no output.

### 5. Confirm the pinned Lean version

Display the project’s toolchain file:

```bash
cat lean-toolchain
```

Expected output:

```text
leanprover/lean4:v4.28.0
```

Now ask Lake for its version:

```bash
lake --version
```

Elan will automatically download Lean 4.28.0 if it is not already installed.

A correct installation reports Lean 4.28.0, for example:

```text
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
```

The exact Lake build identifier may differ, but the Lean version must be `4.28.0`.

### 6. Download the pinned dependencies and Mathlib cache

Run:

```bash
lake exe cache get
```

On the first execution, Lake clones the dependency revisions recorded in `lake-manifest.json` and downloads Mathlib’s compiled cache.

Messages such as the following are normal:

```text
No files to download
Decompressing 8007 file(s)
Completed successfully!
```

or:

```text
Already decompressed 8010 file(s)
```

The exact number of cached files may vary slightly.

For strict reproduction of the committed dependency set, do **not** run `lake update`. The committed `lake-manifest.json` already identifies the dependency revisions that should be used.

### 7. Build the complete Lake project

Run:

```bash
lake build
```

The first build can take several minutes. A successful build ends with a message similar to:

```text
Build completed successfully (8032 jobs).
```

The number of jobs may vary, but the important phrase is:

```text
Build completed successfully
```

Immediately confirm the command’s exit status:

```bash
echo $?
```

Expected output:

```text
0
```

An exit status of `0` means that the project built successfully.

### 8. Verify `Solution.lean` directly

To elaborate the solution file explicitly, run:

```bash
lake env lean Solution.lean
```

Then check the exit status:

```bash
echo $?
```

Expected output:

```text
0
```

Lean may return directly to the Terminal prompt without printing anything. No output together with exit status `0` means that `Solution.lean` was accepted successfully.

### 9. About the `sorry` warnings

During `lake build`, Lean reports sixteen warnings from `Challenge.lean`, for example:

```text
warning: Challenge.lean:52:8: declaration uses `sorry`
```

These warnings are intentional and do not indicate a failed build.

`Challenge.lean` is the statement interface used by the comparator. It contains one placeholder for each of the sixteen declarations being verified. The actual proofs are supplied by `RequestProject/Main.lean` and exposed through `Solution.lean`.

The CI workflow checks that:

1. the trusted proof sources contain no `sorry`, `admit`, or added axiom declarations;
2. the complete Lean project builds;
3. all sixteen declarations in `Solution.lean` match the corresponding declarations in `Challenge.lean`;
4. only the permitted foundational axioms are used.

Therefore, the expected local result is a successful build accompanied by sixteen warnings originating only from `Challenge.lean`.

### 10. Full comparator verification

The project includes:

```text
verify.sh
```

This script runs a pinned Lean comparator and `lean4export` inside the `landrun` sandbox.

The supplied verifier uses a Linux x86-64 `landrun` executable and should not be run directly on macOS. On macOS, use:

```bash
lake build
lake env lean Solution.lean
```

The full sandboxed comparator is run automatically by GitHub Actions:

[View the Sumsquares revised CI workflow](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/workflows/sumsquares-revised-ci.yml)

On a compatible Linux x86-64 system, the complete comparator can be run with:

```bash
bash verify.sh
```

### 11. Rebuilding after later changes

From the repository root, update the local `main` branch:

```bash
git switch main
git pull --ff-only
cd sumsquares_revised
```

Then refresh the cache and rebuild:

```bash
lake exe cache get
lake build
lake env lean Solution.lean
```

A successful reproduction is established when:

```text
Build completed successfully
```

is reported and the final exit status is:

```text
0
```
