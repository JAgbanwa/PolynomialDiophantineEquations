This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# On the polynomial values represented by quadratic forms — Lean formalization

This Lake project contains a complete Lean 4 (Mathlib) formalization of the main results of
the paper *On the polynomial values represented by quadratic forms* by Bogdan Grechuk and
Jamal Agbanwa (`On_the_polynomial_values_represented_by_quadratic_forms_new.pdf`, included in
this repository).

All proofs are complete: the source contains no `sorry`, no `axiom` declarations and no
`@[implemented_by]` attributes, and the main theorems depend only on the standard Lean
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Layout

The project is a standard Lake project with three Lean targets, declared in `lakefile.toml`:
`RequestProject` (the development), `Challenge` (self-contained statements of the main
results) and `Solution` (their proofs).

| File | Contents |
| --- | --- |
| `RequestProject.lean` | The complete development (see the section list below). |
| `Challenge.lean` | Self-contained statements of the main results of the paper, phrased purely in Mathlib terms (`import Mathlib` only). |
| `Solution.lean` | A proof of every `Challenge` statement, from the development. |
| `formalization.yaml` | Correspondence between the numbered results of the paper and the Lean declarations, plus the responses to the referee's Lean comments. |
| `comparator.json` | Machine-readable list of the formalized theorem and definition names, entry modules and toolchain revisions. |
| `verify.sh` | Builds the project and checks that no placeholders or extra axioms are used. |
| `SNAPSHOT.md` | Toolchain and dependency revisions, and the state of the verification. |
| `lean-toolchain`, `lake-manifest.json` | The exact Lean version (`leanprover/lean4:v4.28.0`) and the pinned revisions of Mathlib and its dependencies. |

Inside `RequestProject.lean` the material appears in the following order:

| Part | Contents |
| --- | --- |
| The set `S₂` | Positive integers that are sums of two squares, and property `(*)` of Section 2 (multiplication and cancellation). |
| Pell engine | For a positive non-square `A`, `D ≠ 0` and any modulus `N ≠ 0`, one integer solution of `X² − A V² = D` produces infinitely many with prescribed residues of `X` and `V` modulo `N`. |
| Tools | Squares modulo 4, parity of the two squares in a representation, a non-square criterion, and a transfer lemma for infinite sets. |
| Section 2 | Identity (6) (existence and uniqueness of `Dᵤ`), identity (7), Proposition 2.2 and Proposition 2.3. |
| Section 3 (core) | Algorithm 2.4 specialised to `R(t) = t³ + f` with `Q(x) = x²` and with `Q(w) = 4w²`. |
| Section 3 | `x⁶ + f ∈ S₂` infinitely often for `f ∈ {8, 5, −3, −4}`, Corollary 3.1 and Corollary 3.2. |
| Section 4 | The tangent-line construction, Proposition 4.1, Proposition 4.2, Proposition 4.4, non-multiplicativity of `2y² + yz + 2z²`, and the degenerate case `Δ = 0`. |
| `PolyQF.Main` | The main results of the paper, collected in one place. |

## Main results

* `PolyQF.S2_star` — property `(*)`: for positive `a, b`, if `S₂` contains two of `a`, `b`,
  `ab`, it contains all three.
* `PolyQF.exists_unique_taylorQuot` — identity (6); `PolyQF.identity_seven` — identity (7).
* `PolyQF.prop_2_2` — Proposition 2.2.
* `PolyQF.prop_2_3` — Proposition 2.3 (and `PolyQF.prop_2_3_pairs` for the solution set).
* `PolyQF.S2_x6_sub_4_infinite` — `x⁶ − 4` is a sum of two squares infinitely often.
* `PolyQF.cor_3_1` — equation (2), `y² + x³y + z² + 1 = 0`, has infinitely many integer
  solutions.
* `PolyQF.cor_3_2_eq13`, `PolyQF.cor_3_2_eq14`, `PolyQF.cor_3_2_eq15`,
  `PolyQF.cor_3_2_eq16` — Corollary 3.2 for equations (13)–(16).
* `PolyQF.prop_4_1`, `PolyQF.prop_4_2`, `PolyQF.prop_4_4_a`, `PolyQF.prop_4_4_b` — the
  results of Section 4, together with `PolyQF.degenerate_disc_zero` and
  `PolyQF.BQF_two_one_two_not_represents_four`.

## Conventions and remarks on the formalization

* "Infinitely many" is rendered as `Set.Infinite` of the corresponding solution set. For the
  auxiliary equations, both the set of solutions `(x, v)` and the set of `x`-coordinates are
  shown to be infinite, matching the wording of Propositions 2.2, 2.3 and 4.1.
* `S₂` is `PolyQF.S2 n := 0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2`. The cancellation half of
  property `(*)` uses Fermat's characterization of sums of two squares, available in Mathlib
  as `Nat.eq_sq_add_sq_iff`.
* Proposition 2.3 and Proposition 4.2 are both deduced from the single Pell-type statement
  `PolyQF.pell_solutions_infinite`, which is proved from Mathlib's
  `Pell.exists_of_not_isSquare` by multiplying a given solution by a unit congruent to `1`
  modulo the required modulus.
* In Proposition 4.1 the tangent-line coefficients `λ, μ` of (25) are introduced as integers
  satisfying `2mλ = rp + v(Bp + 2Cq)` and `2mμ = rq − v(2Ap + Bq)`; the congruences (27) are
  exactly what guarantees that such integers exist. `PolyQF.congr_27_of_congr` shows that
  the conclusion of Proposition 4.2 (a congruence `v ≡ v₀ mod 2m`) delivers hypothesis (27)
  of Proposition 4.1.
* Proposition 4.4 is proved by exhibiting the explicit polynomial families given in the
  paper and checking that they satisfy the equations identically (by `ring`), rather than by
  re-running the tangent-line construction; the construction itself is formalized separately
  in `PolyQF.prop_4_1`.
* The Lean proof of Proposition 4.2 does not use Gauss's theorem ([11, Proposition 3.14] of
  the paper) for the conic (30): it completes the square and applies the residue-controlled
  Pell statement `PolyQF.pell_solutions_infinite`, which already produces the solutions in a
  prescribed residue class modulo `2m`. The hypothesis `Δ ≠ 0` is not needed for
  Proposition 4.2 itself. Both points are recorded in the docstrings.
* No `native_decide` (or any other tactic introducing a non-standard axiom) is used. The four
  non-squareness facts of Section 3 (`a = 17006096, 8320, 208, 80`) are proved from the bounds
  stated in the paper (`4123² < a < 4124²`, `91² < a < 92²`, `14² < a < 15²`, `8² < a < 9²`)
  via `PolyQF.not_isSquare_of_between` and `norm_num`.
* Bibliographic citations in the Lean docstrings follow the final bibliography of the paper;
  in particular Gauss's theorem is cited as [11, Proposition 3.14].
* The relation between Section 2 and the general theory of Section 4 — the multiplicativity of
  `y² + z²` and its failure for a general form — is discussed in the "Comparison with
  Section 2" part of `RequestProject.lean`.
* The file opens with three `private` wrapper lemmas (`mem_setOf_eq'`, `finite_setOf_isRoot'`,
  `infinite_sdiff_of_finite`) that stand in for Mathlib results whose names differ between
  Mathlib versions. They are used in place of those library names so that the file elaborates
  with no deprecation warnings on recent Mathlib releases as well.
* Statements of the paper that are prose (Algorithms 2.4 and 4.3, Table 1, and the
  remarks quoting the literature) have no separate Lean counterpart; the mathematical
  content used in the proofs is formalized in the propositions listed above.

## Building

```bash
lake exe cache get   # optional, fetches Mathlib build artifacts
lake build
./verify.sh
```

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

The project pins its dependencies exactly, so builds use the recorded Lean and Mathlib versions:

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

The Lean declaration names retain the numbering of an earlier draft. Their references
in the supplied marked manuscript dated 6 September 2026 are:

| Stable Lean declaration | Marked manuscript reference |
| --- | --- |
| `equation_14_infinite` | Equation (13), Corollary 3.2 |
| `equation_15_infinite` | Equation (14), Corollary 3.2 |
| `equation_16_infinite` | Equation (15), Corollary 3.2 |
| `equation_17_infinite` | Equation (16), Corollary 3.2 |
| `prop_4_5_degenerate_case` | Unnumbered closing discussion of Section 4, equation (32) |

## Building

The manuscript's verified source is commit
`f3203621e90e5b1b087ca473ba8e8a7a2856b009`. To reproduce that build, run the
following from the repository root:

```sh
git fetch origin f3203621e90e5b1b087ca473ba8e8a7a2856b009
git checkout --detach f3203621e90e5b1b087ca473ba8e8a7a2856b009
cd sumsquares_revised
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build RequestProject Solution  # warnings are errors for proved targets
```

This selects the exact checked source as well as its pinned dependencies. See
[SNAPSHOT.md](SNAPSHOT.md) for the immutable project and proof links. Continue
using these instructions after checkout; documentation inside the historical
commit predates this correction.

## Independent verification with `comparator`

On a compatible Linux x86-64 system, after selecting the verified commit and
entering `sumsquares_revised` as above:

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

* **Proposition 4.2** in the revised manuscript substitutes `v = v₀ + 2mw`. For
  `a ≠ 0`, it applies the published conic theorem [11, Proposition 3.14]; the case
  `a = 0` is handled directly. The Lean proof also treats the linear case directly
  and, for `a ≠ 0`, completes the square and uses the residue-controlled Pell lemma
  `genPell_infinite_cong`. The Lean statement also records that the non-degeneracy assumption
  `Δ ≠ 0` is not needed for Proposition 4.2 itself.
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

The verified source is commit `f3203621e90e5b1b087ca473ba8e8a7a2856b009`, with **Lean 4.28.0** and a fixed Mathlib revision through `lean-toolchain` and `lake-manifest.json`. The following instructions select that source before building on macOS using Terminal. They also work on most Linux systems.

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
cd PolynomialDiophantineEquations-build-test
git fetch origin f3203621e90e5b1b087ca473ba8e8a7a2856b009
git checkout --detach f3203621e90e5b1b087ca473ba8e8a7a2856b009
cd sumsquares_revised
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

`git rev-parse HEAD` must print
`f3203621e90e5b1b087ca473ba8e8a7a2856b009`. The checkout is deliberately in
detached HEAD state, so `git branch --show-current` prints nothing. For a fresh
checkout, `git status --short` should also produce no output.

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

### 8. Verify the proof files with warnings treated as errors

To reproduce the strict proof-source checks, run:

```bash
lake env lean -DwarningAsError=true RequestProject/Main.lean
lake env lean -DwarningAsError=true Solution.lean
```

Check the exit status immediately after each command:

```bash
echo $?
```

Expected output:

```text
0
```

Lean may return directly to the Terminal prompt without printing anything. For
each command, no output together with exit status `0` means that the file was
accepted with no errors or warnings.

### 9. About the `sorry` warnings

The default `lake build` builds `RequestProject` and `Solution` with warnings treated
as errors. It does not build the statement-only `Challenge` module. Running
`lake build Challenge` or the comparator script reports sixteen warnings from
`Challenge.lean`, for example:

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

Therefore, the expected default build has no warnings. The separate comparator
run builds `Challenge` and reports sixteen deliberate statement-placeholder
warnings; its success is confirmed by `Your solution is okay!`.

### 10. Full comparator verification

Use the verified checkout from Step 3 for all commands in this section.

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

### 11. Reproducing the verified build again

From the repository root, select the same verified source:

```bash
git fetch origin f3203621e90e5b1b087ca473ba8e8a7a2856b009
git checkout --detach f3203621e90e5b1b087ca473ba8e8a7a2856b009
cd sumsquares_revised
```

Then refresh the cache and rebuild:

```bash
lake exe cache get
lake build
lake env lean -DwarningAsError=true RequestProject/Main.lean
lake env lean -DwarningAsError=true Solution.lean
```

A build of a later `main` revision tests different source code. For reproduction
of the manuscript's verification, keep the commit above and the committed
dependency manifest.

A successful reproduction has the exact HEAD recorded in Step 4, successful
exit statuses for both strict checks, and:

```text
Build completed successfully
```

is reported and the final exit status is:

```text
0
```
