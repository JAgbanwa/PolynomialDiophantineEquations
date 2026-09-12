# On the polynomial values represented by quadratic forms — Lean formalization

This Lake project formalizes the results listed below from *On the polynomial values
represented by quadratic forms* by Bogdan Grechuk and Jamal Agbanwa
([arXiv:2607.06627](https://arxiv.org/abs/2607.06627)). It includes the proof that
`x⁶ − 4` is a sum of two squares for infinitely many integers `x`, the five
Diophantine equations of Corollaries 3.1 and 3.2 with infinitely many integer solutions,
and results about general binary quadratic forms.

For hands-on instructions, start with the
[Terminal and Windows build guide](#verify-the-build-from-terminal-or-windows).

## Verified source and scope

The source snapshot
[`00743362664f95bc747ad9d960499094de7293eb`](https://github.com/JAgbanwa/PolynomialDiophantineEquations/commit/00743362664f95bc747ad9d960499094de7293eb)
passed both jobs in
[GitHub Actions run 34689054241](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/runs/34689054241)
on 12 September 2026:

- The complete Lake project built successfully.
- All four project Lean files elaborated with no errors or warnings.
- The proof-source scan passed, and the axiom audit passed for all **28 listed theorems
  and 16 listed definitions** in [comparator.json](comparator.json).
- Every audited declaration used only a subset of `propext`, `Classical.choice`, and
  `Quot.sound`. The verification script ended with `ALL CHECKS PASSED`.

These results apply to that exact snapshot. The
[current CI history](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/workflows/sumsquares-revised-ci.yml)
records checks of later commits.

The mathematical scope is the statements expressed in the Lean files. Compiling them
checks their proofs, but does not itself verify their correspondence with every sentence
or every version of the manuscript. Algorithms 2.4 and 4.3 are represented through their
supporting propositions and worked instances; there is no separate general algorithm
correctness theorem. Table 1 and bibliographic discussion are not separate formal results.

## Project layout

[lakefile.toml](lakefile.toml) declares three default library targets:
`RequestProject`, `Challenge`, and `Solution`.

| File | Role |
| --- | --- |
| [RequestProject/Main.lean](RequestProject/Main.lean) | The mathematical development in `PolyQF`, followed by the main result statements in `PolyQF.Main`. |
| [RequestProject.lean](RequestProject.lean) | The entry point: it imports `RequestProject.Main`. |
| [Challenge.lean](Challenge.lean) | Twelve result statements defined as propositions, plus the `IsSumTwoSquares` predicate. It imports only `Mathlib` and contains no placeholder proofs. |
| [Solution.lean](Solution.lean) | Proofs of all twelve `Challenge` result statements, plus an equivalence lemma for the sum-of-two-squares predicates. |
| [comparator.json](comparator.json) | The verification manifest: 16 `PolyQF.Main` theorems, 12 `Solution` theorems, 16 definitions, and the allowed axiom names. |
| [verify.sh](verify.sh) | The build, proof-source, and axiom audit described below. |
| [formalization.yaml](formalization.yaml) | A catalog of results, numbered references, and notes addressing the referee's formalization comments. |
| [SNAPSHOT.md](SNAPSHOT.md) | Additional dependency and verification notes. The immutable source and successful run are linked above. |
| [lean-toolchain](lean-toolchain), [lake-manifest.json](lake-manifest.json) | The Lean toolchain and exact dependency revisions. |

`Challenge.lean` defines propositions; it does not assume them as axioms. For example,
`Solution.equation2` has type `Challenge.Equation2`, and Lean checks its proof against
that type when compiling `Solution.lean`.

## Mathematical results

The numbering below follows the **current Lean source and result catalog**. Use the
explicit statements when comparing with a manuscript version whose numbering differs.

| Result | Lean declaration |
| --- | --- |
| Property (*): for positive `a, b`, membership of two of `a`, `b`, `ab` in `S₂` implies membership of the third | `PolyQF.S2_star` |
| Identity (6): existence and uniqueness of the Taylor quotient `Dᵤ` | `PolyQF.exists_unique_taylorQuot` |
| Identity (7) | `PolyQF.identity_seven` |
| Proposition 2.2 | `PolyQF.Main.proposition_2_2` |
| Proposition 2.3: infinitely many `x` satisfying the quadratic equation under its stated hypotheses | `PolyQF.Main.proposition_2_3` |
| `x⁶ − 4` is a sum of two squares infinitely often | `PolyQF.Main.x_pow_six_sub_four_sum_two_squares` |
| Proposition 4.1: the general quadratic-form construction under its stated hypotheses | `PolyQF.Main.proposition_4_1` |
| Proposition 4.2: infinitely many solution pairs `(x, v)` with `2m ∣ v − v₀`, under its stated hypotheses | `PolyQF.Main.proposition_4_2` |
| `2y² + yz + 2z²` represents `2` but not `4` | `PolyQF.Main.form_2_1_2_not_multiplicative` |
| A form with discriminant zero is `k(ny + mz)²` for integer `k, n, m` | `PolyQF.Main.degenerate_case` |

Each equation in the following table has an infinite set of integer triples `(x, y, z)`:

| Reference in the source | Equation | Lean declaration |
| --- | --- | --- |
| Corollary 3.1, (2) | `y² + x³y + z² + 1 = 0` | `PolyQF.Main.equation_2_infinite` |
| Corollary 3.2, (13) | `y² + x³y + z² − 2 = 0` | `PolyQF.Main.equation_13_infinite` |
| Corollary 3.2, (14) | `y² + x³y + z² + z − 1 = 0` | `PolyQF.Main.equation_14_infinite` |
| Corollary 3.2, (15) | `y² + x³y + z² + z + 1 = 0` | `PolyQF.Main.equation_15_infinite` |
| Corollary 3.2, (16) | `y² + x³y + y + z² + 1 = 0` | `PolyQF.Main.equation_16_infinite` |
| Proposition 4.4(a), (31)(a) | `2y² + yz + 2z² = x³ + 1` | `PolyQF.Main.equation_31a_infinite` |
| Proposition 4.4(b), (31)(b) | `2y² + yz + 2z² = x³ − 1` | `PolyQF.Main.equation_31b_infinite` |

The development also proves the even-`x` families for `x⁶ + 8`, `x⁶ + 5`, and `x⁶ − 3`,
and the example that `4(y² + z²)` represents `4` but not `1`.

### Proof organization and conventions

- `PolyQF.S2 n` means `0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2`.
  “Infinitely many” is expressed using `Set.Infinite`. Proposition 2.3 has both an
  infinite-`x` theorem and a separate infinite-pairs theorem, `PolyQF.prop_2_3_pairs`.
- The cancellation part of property (*) uses Mathlib's sum-of-two-squares
  characterization `Nat.eq_sq_add_sq_iff`.
- `PolyQF.pell_solutions_infinite` builds on Mathlib's `Pell.exists_of_not_isSquare`.
  It produces infinitely many solutions to a generalized Pell equation in the same
  residue classes as a given integer solution, modulo a chosen nonzero modulus. Propositions 2.3 and 4.2 use it in their nonlinear cases; their
  `a = 0` cases are handled by explicit families.
- In the nonlinear case, the Lean proof of Proposition 4.2 completes the square and
  uses that Pell result.
  The formal statement permits `D = 0` and concludes infinitude of pairs `(x, v)`;
  it does not assert infinitely many distinct `x` in every such case. This is a
  proof-level distinction from the manuscript's use of a published conic theorem.
- `PolyQF.congr_27_of_congr` transfers the required divisibility conditions from `v₀`
  to `v` when `2m ∣ v − v₀`, assuming those conditions hold for the seed `v₀`.
- Proposition 4.4 is proved using explicit polynomial families: `ring` verifies the
  identities, and an injectivity argument establishes infinitude. The tangent-line
  construction is formalized separately in `PolyQF.prop_4_1`.
- The four non-square constants `17006096`, `8320`, `208`, and `80` are handled with
  `PolyQF.not_isSquare_of_between` and `norm_num`, using the respective bounds
  `4123² < 17006096 < 4124²`, `91² < 8320 < 92²`, `14² < 208 < 15²`, and
  `8² < 80 < 9²`. The project proof sources do not use `native_decide`.

## Versions and prerequisites

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.28.0` |
| Mathlib | Tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Lake | Bundled with the pinned Lean toolchain |

The committed `lake-manifest.json` pins Mathlib and all transitive dependency revisions.
Keep it unchanged when reproducing this source; `lake update` can change dependency
resolution. Verification here establishes compatibility with the pinned toolchain.

## Verify the build from Terminal or Windows

Choose the route for your computer. **Run commands one line at a time, wait for each
command to finish, and stop if it reports an error.** Commands inside `bash` blocks
belong in macOS/Linux Terminal or Ubuntu under WSL; `powershell` blocks belong in
PowerShell. The first download and build can take several minutes.

| Your system | Guide | What it verifies |
| --- | --- | --- |
| macOS or Linux | [Terminal steps](#macos-and-linux-terminal) | Lean build and full proof/axiom audit |
| Windows 10/11 | [WSL/Ubuntu steps](#windows-full-verification-with-wsl) | Lean build and full proof/axiom audit; recommended Windows route |
| Windows, without WSL | [Native PowerShell steps](#windows-native-powershell-build) | Lean build; use WSL for `verify.sh` |

CI runs on Ubuntu 24.04. Its passing result is evidence for that environment; it is
not a record of a native macOS or Windows test.

### macOS and Linux Terminal

#### 1. Install the prerequisites for your system

**macOS:** open **Terminal** (Applications → Utilities). Run:

```bash
git --version
curl --version
```

If macOS offers to install Xcode Command Line Tools, complete that installation.
Install [Homebrew](https://brew.sh/) if `brew --version` is unavailable, and follow
the installer's printed **Next steps** to make `brew` available in this Terminal.
Then install Python and GNU grep:

```bash
brew install python grep
export PATH="$(brew --prefix grep)/libexec/gnubin:$PATH"
python3 --version
grep --version
```

The last command should identify **GNU grep**. The PATH command selects the
[Homebrew GNU grep](https://formulae.brew.sh/formula/grep) needed by the audit's text
scan; repeat it in a new Terminal before running the audit.

**Ubuntu/Debian Linux, including Ubuntu under WSL:** open a terminal and run:

```bash
sudo apt update
sudo apt install -y git curl python3 build-essential ca-certificates unzip grep
```

On another Linux distribution, install the equivalent packages with its package manager.

#### 2. Install Elan and activate it in this terminal

If `elan --version` already works, keep that installation. Otherwise use the
[official Elan installer](https://github.com/leanprover/elan#installation):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Choose the default installation option when prompted. With the default installation
location, activate Elan for this terminal and check it:

```bash
source "$HOME/.elan/env"
elan --version
```

Elan supplies both `lean` and `lake` and selects the version in this project's
`lean-toolchain` file. No editor or VS Code installation is needed for these checks.

#### 3. Obtain a fresh checkout and check the location/version

These commands create a new folder in your home directory. If the example folder
already exists, choose a different new folder name in both the `git clone` and `cd`
commands. In WSL, this uses Ubuntu's home directory.

```bash
cd "$HOME"
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-terminal-check
cd PolynomialDiophantineEquations-terminal-check/sumsquares_revised
pwd
ls lean-toolchain lakefile.toml verify.sh
cat lean-toolchain
lean --version
git rev-parse HEAD
```

`pwd` must end in `/sumsquares_revised`, `cat lean-toolchain` must print
`leanprover/lean4:v4.28.0`, and `lean --version` must report **4.28.0**. Elan downloads
that version on first use if needed. Record the commit printed by `git rev-parse HEAD`:
these instructions test the current checkout, which may be newer than the
[verified snapshot](#reproduce-the-verified-snapshot).

#### 4. Download the dependencies and build

First fetch Mathlib's compiled cache:

```bash
lake exe cache get
echo "Cache exit code: $?"
```

Continue only when the cache command succeeds and the displayed exit code is `0`.
Then build all three targets (`RequestProject`, `Challenge`, and `Solution`):

```bash
lake build
echo "Build exit code: $?"
```

**The build passed when both of these are true:** Lake reports
`Build completed successfully` and the next line reports `Build exit code: 0`.
The job count in the success message can vary. A nonzero exit code or a reported
build failure means the build has not passed.

#### 5. Run the full proof and axiom audit

Remain in the same `sumsquares_revised` directory and run:

```bash
bash verify.sh
echo "Audit exit code: $?"
```

**The full audit passed when it ends with `ALL CHECKS PASSED` and
`Audit exit code: 0`.** This checks the four proof files with warnings treated as
errors and checks the 44 declarations listed in the verification manifest.
`SOME CHECKS FAILED`, `FAIL:`, or a nonzero exit code needs investigation.

The exit-code command must immediately follow the command being checked. Running
another command first replaces `$?` with that other command's status.

### Windows: full verification with WSL

This is the recommended Windows route for running the same Bash audit as CI.
[Microsoft's WSL installation guide](https://learn.microsoft.com/en-us/windows/wsl/install)
provides the supported Windows versions and additional setup details.

1. If Ubuntu under WSL is not installed, open **PowerShell as Administrator** and run:

   ```powershell
   wsl --install -d Ubuntu
   ```

2. Restart Windows if requested. Open **Ubuntu** from the Start menu and complete
   the first-run Linux username/password setup. If Ubuntu was already installed,
   you can open it from a normal PowerShell window with:

   ```powershell
   wsl -d Ubuntu
   ```

3. In the **Ubuntu** window, run:

   ```bash
   cd ~
   ```

4. Follow **Steps 1–5 in the [Terminal guide](#macos-and-linux-terminal)** above,
   selecting the **Ubuntu/Debian** prerequisite commands in Step 1. Run all of those
   commands inside Ubuntu, including the Elan installation and the fresh clone.
   The final success markers are `Build completed successfully`,
   `ALL CHECKS PASSED`, and exit codes of `0`.

Keep this checkout in the [Linux filesystem](https://learn.microsoft.com/en-us/windows/wsl/filesystems),
such as `/home/yourname`, as the commands above do. Unrelated folders elsewhere in
this repository have names with trailing spaces that are unsuitable for a normal
Windows-filesystem checkout. WSL uses its own Lean installation and build cache.

### Windows: native PowerShell build

These steps check the Lean build directly in Windows. The full `verify.sh` audit
uses Bash, GNU utilities, and `python3`; use the WSL route above for that audit.

#### 1. Install Git and Elan

Open **PowerShell** from the Start menu or select a PowerShell tab in Windows Terminal.
Check:

```powershell
git --version
curl.exe --version
```

If Git is missing, install [Git for Windows](https://git-scm.com/download/win), then
close and reopen PowerShell. If `curl.exe` is missing, follow Lean's
[Windows installation prerequisites](https://lean-lang.org/install/manual/).

If `elan --version` does not work, install Elan with its
[official Windows installer](https://github.com/leanprover/elan/blob/master/elan-init.ps1).
Run the following in a folder where you can save the installer:

```powershell
curl.exe -sSfL https://elan.lean-lang.org/elan-init.ps1 -o elan-init.ps1
powershell.exe -NoProfile -ExecutionPolicy Bypass -File .\elan-init.ps1 -DefaultToolchain none
```

Choose the default installation option if prompted, then close and reopen PowerShell
so the installer’s PATH changes take effect. Check:

```powershell
elan --version
Get-Command git, lean, lake -ErrorAction Stop
```

#### 2. Check out only this project

Use a **sparse checkout** so Git does not try to create unrelated folders with
Windows-incompatible names. If the example folder exists, use a different new name.

```powershell
Set-Location $env:USERPROFILE
git clone --sparse https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-powershell-check
Set-Location PolynomialDiophantineEquations-powershell-check
git sparse-checkout set sumsquares_revised
Set-Location sumsquares_revised
Get-Location
Get-Content lean-toolchain
lean --version
git rev-parse HEAD
```

The directory must end in `sumsquares_revised`; Lean must report **4.28.0**. Record
this commit to identify exactly which source you are checking. Sparse checkout
retains the project files and their contents; it only limits the folders materialized
locally. See [Git's sparse-checkout documentation](https://git-scm.com/docs/git-sparse-checkout).

#### 3. Download the cache and build

Run the cache command, then inspect its exit code immediately:

```powershell
lake exe cache get
"Cache exit code: $LASTEXITCODE"
```

Continue only if the command succeeds and its exit code is `0`. Then run:

```powershell
lake build
"Build exit code: $LASTEXITCODE"
```

**The native Windows build passed when Lake reports `Build completed successfully`
and PowerShell prints `Build exit code: 0`.** In PowerShell,
[`$LASTEXITCODE`](https://learn.microsoft.com/en-us/powershell/module/microsoft.powershell.core/about/about_automatic_variables#lastexitcode)
is the numeric exit code of the last native program; it is different from PowerShell's
Boolean `$?`. Read it immediately after `lake`. A successful `lake build` alone does
not establish that the separate axiom audit passed.

### Troubleshooting

| Symptom | What to do |
| --- | --- |
| `lean` or `lake` is not found in Terminal/Ubuntu | Run `source "$HOME/.elan/env"` for the default Elan installation, then retry. |
| `lean` or `lake` is not found in PowerShell | Close and reopen PowerShell after installing Elan. Check `Get-Command lean, lake`. |
| “No default toolchain configured” or the wrong Lean version | Enter the `sumsquares_revised` folder before running `lean`; check `lean-toolchain` there. |
| Lake cannot find the package configuration | Check your location. `lakefile.toml` must be in the current directory. |
| Git reports `invalid path` on Windows | Use the native sparse-checkout commands or a fresh clone in WSL's Linux home directory. |
| `python3` is missing or the macOS audit has grep errors | Complete the prerequisite step; on macOS select GNU grep using the documented PATH command. |
| A dependency/cache download fails | Resolve the displayed network/download error, then rerun `lake exe cache get` before building. |
| A file produces an error/warning, or the audit reports `FAIL:` | Keep the first error and surrounding output, plus `git rev-parse HEAD` and `lean --version`, when reporting the failure. |

Avoid `lake update` when reproducing the pinned build: it changes dependency resolution
rather than checking the committed dependency set.

## What the audit checks

[verify.sh](verify.sh) performs three checks:

1. It builds the project and elaborates every `.lean` file under `RequestProject/`,
   plus `RequestProject.lean`, `Challenge.lean`, and `Solution.lean`, with
   `-DwarningAsError=true`. Any failed invocation or diagnostic output fails the audit.
2. It scans these sources for `sorry`, `admit`, axiom declarations,
   `@[implemented_by]`, and `native_decide`. The explanatory source-comment line
   stating that `native_decide` is not used is excluded from this text scan.
3. It imports the project modules and runs `#print axioms` for all names in
   `definition_names` and `theorem_names` in `comparator.json`. Missing results,
   unrecognized output, or an axiom outside the configured standard allowlist fail
   the audit. These lists currently contain 44 distinct declarations.

The axiom check includes the dependencies of the listed declarations; it is not a
separate enumeration of every auxiliary lemma in the project. `lake build` alone does
not perform this audit or globally enable warnings-as-errors; use `bash verify.sh`
for the stricter checks.

Despite its filename, `comparator.json` is currently used as an audit manifest.
`verify.sh` does **not** invoke `comparator`, `lean4export`, `landrun`, or `nanoda`.
It does not perform an independent exported-proof replay or compare separate challenge
and solution environments. The `Challenge`/`Solution` relationship is checked by Lean
when compiling the twelve proofs against their declared proposition types.

The [CI workflow](../.github/workflows/sumsquares-revised-ci.yml) runs a project build
and then a separate proof-source and axiom audit. The expected successful result is
that both jobs pass, with no intentional placeholder warnings.

## Reproduce the verified snapshot

After completing the platform setup above, use the following commands in macOS/Linux
Terminal or Ubuntu under WSL to reproduce the successful run linked above. They use a
separate clone and select its exact source commit:

```bash
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-verified
cd PolynomialDiophantineEquations-verified
git checkout --detach 00743362664f95bc747ad9d960499094de7293eb
cd sumsquares_revised
lake exe cache get
echo "Cache exit code: $?"
bash verify.sh
echo "Audit exit code: $?"
git rev-parse HEAD
```

Continue past each verification command only when it succeeds with exit code `0`.
The audit must report `ALL CHECKS PASSED`. The final command must print
`00743362664f95bc747ad9d960499094de7293eb`.

For native PowerShell, use the sparse checkout above, then run
`git checkout --detach 00743362664f95bc747ad9d960499094de7293eb` from the repository
root before repeating the native cache/build steps. Check `$LASTEXITCODE` after each.
The checkout is intentionally detached. Immutable references for this snapshot are:

- [Project folder](https://github.com/JAgbanwa/PolynomialDiophantineEquations/tree/00743362664f95bc747ad9d960499094de7293eb/sumsquares_revised)
- [Main proof file](https://github.com/JAgbanwa/PolynomialDiophantineEquations/blob/00743362664f95bc747ad9d960499094de7293eb/sumsquares_revised/RequestProject/Main.lean)

## Credits and licence

The project acknowledges [Aristotle](https://aristotle.harmonic.fun) (Harmonic) for work
on the Lean proofs. The repository currently has no `LICENSE` file; a project licence
has not been recorded.
