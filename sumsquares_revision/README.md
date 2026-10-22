# Lean formalisation: “On the polynomial values represented by binary quadratic forms”

Lean formalisation of the paper by Bogdan Grechuk and Jamal Agbanwa, IJNT manuscript
IJNT-D-26-00150. This project uses **Lean 4.35.0** and **Mathlib v4.35.0**, with all
resolved dependency revisions committed in `lake-manifest.json`.

**Want to check the Lean proofs?** Start with the
[MacBook and Windows instructions](#practical-instructions-for-macbook-and-windows-users).
The browser option runs the complete verification without installing Lean on
your computer. Separate instructions below also explain how to build locally.

## Verification and paper snapshot

**The complete build and the official comparator passed on 22 October 2026.**
The [completed verification run](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/runs/39761112134)
checked the 42 advertised statements with the real sandbox enabled and then
built every project target. Lean 4.35.0 uses Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` in this project.

| Check | Observed result |
| --- | --- |
| Required files and both 42-theorem inventories | Passed |
| Official v0.4 metadata schema | Passed |
| `lake comparator --config comparator.json` | `Lean default kernel accepts the solution`; `Your solution is okay!` |
| `lake build RequestProject Challenge Solution` | `Build completed successfully (9052 jobs).` |
| Complete `bash verify.sh` | Exit code 0; `==> all checks passed` |
| Built-in axiom audit of all 42 proved declarations | Exactly the union `{propext, Quot.sound, Classical.choice}`; no `sorryAx` |

**Paper snapshot:** `85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab`.

- [Project snapshot](https://github.com/JAgbanwa/PolynomialDiophantineEquations/tree/85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab/sumsquares_revision)
- [Proof development](https://github.com/JAgbanwa/PolynomialDiophantineEquations/blob/85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab/sumsquares_revision/RequestProject/Main.lean)

Use these two links together in the manuscript. They identify one immutable
verified project, including the challenge, solution, metadata, and dependency
pins. The directory `sumsquares_revised` contains a separate, older development.
Later documentation-only commits may record this snapshot without changing its
Lean sources or verification configuration.

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
| `../.github/workflows/sumsquares-revision-ci.yml` | CI verification of this directory |

## Practical instructions for MacBook and Windows users

Choose **one** starting route. Option A is the easiest way to run the complete
check on either computer: GitHub supplies the Linux machine and runs the commands.

| Your goal | Start here |
| --- | --- |
| Check the build and the official comparator in a web browser, on Mac or Windows | [A. Use GitHub Actions](#a-use-github-actions-on-a-macbook-or-windows-computer) |
| Build the Lean formalisation on your MacBook | [B. Build locally on a MacBook](#b-build-locally-on-a-macbook) |
| Build the Lean formalisation on Windows using Ubuntu through WSL 2 | [C. Build locally on Windows](#c-build-locally-on-windows) |
| Run the complete comparator locally in Ubuntu, including a suitable WSL 2 installation | [D. Complete verification in Ubuntu](#d-complete-verification-in-ubuntu) |

**What the two checks mean:** the build compiles `RequestProject`, `Challenge`,
and `Solution`. The complete verification also compares all 42 statements and
checks the solution's permitted axioms with the official comparator. The
comparator's sandbox requires Linux; a successful native Mac build should be
reported as a build result. Option A provides the complete check for Mac users.

For a local installation, allow several gigabytes of free disk space and keep
an internet connection during the initial downloads. Copy only the commands
inside each code box, without the surrounding backticks. Press **Return** on
Mac or **Enter** on Windows and wait for the command to finish. If an error
appears, resolve it before proceeding; see [Troubleshooting](#troubleshooting).

### A. Use GitHub Actions on a MacBook or Windows computer

This route uses Safari, Edge, Chrome, Firefox, or another web browser. No local
Lean installation or terminal is required.

#### A1. Inspect the successful verification of the exact paper snapshot

1. Sign in to GitHub, then open the [paper snapshot's completed verification run](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/runs/39761112134).
2. Select the job **Build and compare the paper statements**.
3. Expand **Run the real comparator and full project build**.
4. Confirm that the job is green and its output contains all four messages below.
5. To save the evidence, return to the run's **Summary**, scroll to **Artifacts**,
   and download `sumsquares-revision-verification-85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab`.
   Sign in to GitHub to download it. The ZIP contains the sandbox, environment,
   and verification logs; save it before the artifact's 90-day retention expires.

The successful run includes:

```text
Lean default kernel accepts the solution
Your solution is okay!
Build completed successfully (9052 jobs).
==> all checks passed
```

The number of build jobs can differ on another run. These messages establish
both the comparator result and **“Build completes successfully.”**

#### A2. Run a new verification

1. Sign in to GitHub and open the [Sumsquares revision verification workflow](https://github.com/JAgbanwa/PolynomialDiophantineEquations/actions/workflows/sumsquares-revision-ci.yml).
2. Click **Run workflow**, select the branch **main**, then click the green
   **Run workflow** button in that menu.
3. Wait for the new run to appear; refresh the page if needed. Open that run.
4. Open **Build and compare the paper statements**. Wait until the job finishes.
5. Expand **Run the real comparator and full project build** and check the four
   messages in A1. A yellow/in-progress or red/failed job is not a completed pass.
6. Download the artifact from **Summary → Artifacts**. Its name ends with the
   commit that was checked. Keep `build-environment.log` and `verification.log`
   together so the result can be traced to that revision.

**If you cannot see “Run workflow”:** starting a run in this repository requires
write access. You can still inspect the linked completed run. To run the checks
in your own GitHub account, open the [repository](https://github.com/JAgbanwa/PolynomialDiophantineEquations),
click **Fork → Create fork**, open your fork's **Actions** tab, enable workflows
if prompted, select **Sumsquares revision verification**, and follow A2 there.

A new run on `main` checks the current `main` commit. The fixed snapshot cited
in the manuscript is the commit in A1. Old red runs remain in the history after
a fix; check the run's revision and result. The separate workflow for the older
`sumsquares_revised` directory does not verify this package.

GitHub's official guides explain [manual runs](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/manually-run-a-workflow)
and [artifact downloads](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts).

### B. Build locally on a MacBook

These steps use macOS Terminal and the release of Lean pinned by this project.
Lean 4.35.0 provides binaries for Apple Silicon and Intel Macs; its
[platform documentation](https://lean-lang.org/doc/reference/4.35.0/platforms/)
describes the support level for each. The full comparator check is available
through [Option A](#a-use-github-actions-on-a-macbook-or-windows-computer).

#### B1. Open Terminal and prepare Git

Press **Command–Space**, type **Terminal**, and press **Return** (see
[Apple's Terminal guide](https://support.apple.com/guide/terminal/open-or-quit-terminal-apd5265185d-f365-44cb-8b09-71a064a42125/mac)).
In that window, run the following command to use Bash for this guide:

```bash
bash
```

Keep this terminal open for the remaining Mac steps. Check that Git is available:

```bash
git --version
```

If macOS asks to install **Command Line Tools**, accept the installation and
wait for it to finish, then run `git --version` again. If no installation dialog
appears and Git is unavailable, run `xcode-select --install` and finish the
dialog. You are ready when `git --version` prints a version number.

#### B2. Install Elan, the Lean version manager

Run these lines in the same Terminal window, one at a time:

```bash
cd "$HOME"
curl -fsSL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
source "$HOME/.elan/env"
elan --version
```

The last line should print an Elan version. If Elan is already installed, you
can start with the `source` line. The project will select its own Lean version.
See the [official Lean installation guide](https://lean-lang.org/install/manual/).

#### B3. Download the paper's exact project

Run each line in order:

```bash
cd "$HOME"
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-paper
cd PolynomialDiophantineEquations-paper
git checkout --detach 85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab
git rev-parse HEAD
cd sumsquares_revision
pwd
```

`git rev-parse HEAD` must print
`85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab`. The “detached HEAD” message is normal:
it means you selected the fixed paper revision. `pwd` must end with
`PolynomialDiophantineEquations-paper/sumsquares_revision`. Keep running the
remaining commands in that directory.

If the clone says that the destination already exists, stop and use the
[existing-folder instructions](#troubleshooting) below; keep any existing work.

#### B4. Install the pinned Lean version and download Mathlib's cache

```bash
cat lean-toolchain
elan toolchain install leanprover/lean4:v4.35.0
lean --version
lake --version
lake exe cache get
```

The first command must print `leanprover/lean4:v4.35.0`, and `lean --version`
must report **4.35.0**. The cache download can take several minutes or longer;
wait for the terminal prompt to return. Preserve `lake-manifest.json` and use
the pinned dependencies; do not run `lake update` to reproduce this snapshot.

#### B5. Build and save the result

Copy and run this **whole block**, including the opening and closing parentheses:

```bash
(
  set -euo pipefail
  lake build RequestProject Challenge Solution 2>&1 | tee build.log
  printf 'Build exit code: 0\n' | tee -a build.log
)
```

Success means that you see a line beginning **`Build completed successfully`**
and the final line **`Build exit code: 0`**. The block saves the output in
`build.log` and prints the final success line only if the build succeeds.
To locate that log in Finder, run `open .` in the same terminal.

Warnings about deliberate `sorry` placeholders in `Challenge.lean` are expected;
see the explanation under [Troubleshooting](#troubleshooting). For the complete
statement comparison and axiom check, follow Option A.

### C. Build locally on Windows

Use **Windows 11**, or **Windows 10 version 2004/build 19041 or later**, with
**Windows Subsystem for Linux (WSL 2)**. This lets you run Ubuntu in a window
alongside your Windows applications. Option A is available if you cannot install
WSL on your computer. These steps follow [Microsoft's WSL installation guide](https://learn.microsoft.com/en-us/windows/wsl/install).

#### C1. Install Ubuntu through WSL 2

Open **Start**, type **PowerShell**, right-click **Windows PowerShell**, and
choose **Run as administrator**. Approve the Windows prompt. In that PowerShell
window, run:

```powershell
wsl --install -d Ubuntu-22.04
```

Wait for installation to finish and restart Windows when requested. If Ubuntu
22.04 is already installed, continue to C2 to check its WSL version.

#### C2. Open Ubuntu and check the WSL version

Open **Start → Ubuntu 22.04 LTS**. On first launch, wait for setup, then choose
a Linux username and password. These are for Ubuntu. **Nothing appears while
you type the password; this is normal.** Remember it for the `sudo` commands.

In a **PowerShell** window, check the installation:

```powershell
wsl --list --verbose
```

The `Ubuntu-22.04` row must show **2** in the **VERSION** column. If it shows 1,
run `wsl --set-version Ubuntu-22.04 2` in PowerShell and wait for it to finish.
Then return to the **Ubuntu** window.

**From C3 onward, type every command in Ubuntu.** The `sudo`, `source`, and
`lake` commands below are Bash commands for that window.

#### C3. Install the required tools in Ubuntu

```bash
cd "$HOME"
sudo apt-get update
sudo apt-get install -y git curl ca-certificates build-essential
```

If `sudo` asks for a password, type the Ubuntu password from C2 and press Enter.
Keep the project in Ubuntu's home directory, as these commands do. Microsoft's
[WSL setup guide](https://learn.microsoft.com/en-us/windows/wsl/setup/environment)
recommends the Linux filesystem when using Linux build tools.

#### C4. Install Elan inside Ubuntu

```bash
curl -fsSL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
source "$HOME/.elan/env"
elan --version
```

The last command must print an Elan version. If Elan is already installed in
Ubuntu, start with the `source` line. A separate Windows installation of Lean
does not replace this Ubuntu setup.

#### C5. Download the exact paper snapshot and its dependencies

Run each line in order in **Ubuntu**:

```bash
cd "$HOME"
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-paper
cd PolynomialDiophantineEquations-paper
git checkout --detach 85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab
git rev-parse HEAD
cd sumsquares_revision
pwd
```

The commit must be `85b3903f4af4424be7939ff9eaee3b6c0dd2c7ab`; “detached HEAD” is
normal for this fixed snapshot. The path printed by `pwd` must end with
`PolynomialDiophantineEquations-paper/sumsquares_revision`. If the clone reports
an existing folder, stop and consult [Troubleshooting](#troubleshooting).

Stay in that directory and run:

```bash
cat lean-toolchain
elan toolchain install leanprover/lean4:v4.35.0
lean --version
lake --version
lake exe cache get
```

`cat lean-toolchain` must show `leanprover/lean4:v4.35.0`; `lean --version` must
report **4.35.0**. Wait for the cache download to finish. Keep the committed
dependency files and avoid `lake update` when reproducing the paper.

For complete local verification, you can go directly to
[Option D](#d-complete-verification-in-ubuntu) now. It includes the full build,
after running the comparator.

#### C6. Build and save the result

Copy and run this **whole block** in Ubuntu:

```bash
(
  set -euo pipefail
  lake build RequestProject Challenge Solution 2>&1 | tee build.log
  printf 'Build exit code: 0\n' | tee -a build.log
)
```

Look for **`Build completed successfully`** and **`Build exit code: 0`**. The
number of jobs can vary. The saved `build.log` is in the current directory.
To open that folder in Windows File Explorer, run `explorer.exe .` from Ubuntu.

This completes the local build. To perform the complete comparator verification,
use Option A, or continue to D in the same Ubuntu window. WSL 2 can run Linux
tools, but the comparator also needs permission to create its sandbox; D1 checks
whether your particular environment permits it.

### D. Complete verification in Ubuntu

This procedure is for an Ubuntu Bash terminal, including a suitable Windows
WSL 2 installation. On a MacBook, use Option A for the complete check. The
published successful CI run uses Ubuntu 22.04.

**Windows users:** first complete C1–C5, then return here with the Ubuntu window
open in `sumsquares_revision`. **Users of a separate Ubuntu machine:** first
follow C3–C5 in its Bash terminal to install the tools and obtain the pinned
project and cache.

#### D1. Install and test the comparator sandbox

```bash
sudo apt-get update
sudo apt-get install -y bubblewrap python3 python3-venv
bwrap --version
bwrap --unshare-all --ro-bind / / --proc /proc --dev /dev -- /bin/true
echo $?
```

The sandbox test normally prints nothing. The final `echo $?` must print **0**.
If it prints another number, or you see `Operation not permitted`, use Option A
for complete verification. Some WSL, container, and hosted environments block
the required operations. Keep the real sandbox enabled; an axiom-only diagnostic
does not substitute for the comparator. See the
[official comparator documentation](https://lean-lang.org/doc/reference/4.35.0/Build-Tools-and-Distribution/Lake/#lake-comparator).

#### D2. Install the metadata validator

Run this from `sumsquares_revision`. The virtual environment below is a separate
folder for the required Python packages, outside the Git checkout:

```bash
python3 -m venv "$HOME/sumsquares-verification-venv"
source "$HOME/sumsquares-verification-venv/bin/activate"
python3 -m pip install -r scripts/requirements.txt
python3 scripts/check_project.py
python3 scripts/check_metadata.py
```

Expected messages include:

```text
OK: 42 named statements in each interface; proof sources contain no placeholders or extra axioms.
OK: formalization.yaml conforms to the pinned v0.4 schema.
```

The schema is an unmodified, pinned copy of the
[official v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json).
Its source and license are recorded in `scripts/schema/README.md`.

#### D3. Run every verification stage and save the logs

Copy and run the **entire block**. Keep the parentheses and `set -euo pipefail`:
they ensure that a failed command cannot be hidden by the log-saving command.

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

`verify.sh` checks the source inventory and metadata, runs
**`lake comparator --config comparator.json`**, and then runs
**`lake build RequestProject Challenge Solution`**. Lean 4.35 supplies the
comparator and exporter. No separately installed comparator is needed.

Success requires the four messages shown in A1, followed by
**`Verification exit code: 0`**. Save `build-environment.log` and
`verification.log` from the current directory as evidence. A cache download or
an ordinary build alone does not establish that this complete check passed.

### Troubleshooting

| What you see | What to do |
| --- | --- |
| `lake`, `lean`, or `elan`: command not found | In Mac Terminal or Ubuntu, run `source "$HOME/.elan/env"`, then retry. On Windows, check that you are using the Ubuntu window. |
| `sudo` or `source` is not recognised in PowerShell | Open **Ubuntu 22.04 LTS** and resume the Windows instructions there from C3. |
| The clone destination already exists | Keep that folder. To make a separate copy, use `PolynomialDiophantineEquations-paper-2` as the destination in `git clone`, and use that same name in the following `cd` command. |
| `lean-toolchain`, `lakefile.toml`, or `verify.sh` cannot be found | Run `pwd`. Enter the `sumsquares_revision` folder inside the checkout you created. This package has **revision**, not **revised**, in its name. |
| A message says “detached HEAD” | This is expected after selecting the immutable paper commit. Continue with the next step. |
| A password prompt appears but typing shows nothing | Type the password and press Enter. Terminal password entry hides the characters. In Ubuntu, use the Linux password you created in C2. |
| Warnings mention `sorry` in `Challenge.lean` | These are deliberate specification placeholders. The completed proofs are in `Solution.lean` and `RequestProject/Main.lean`; the comparator rejects `sorryAx` in their proof dependencies. |
| Download/cache failure or insufficient disk space | Resolve the network or disk-space problem, then rerun `lake exe cache get` from `sumsquares_revision` before rebuilding. |
| `bwrap` reports `Operation not permitted`, including a loopback error | Use Option A for complete verification. This is a sandbox-environment failure; the local build result and comparator result are separate checks. |
| An older GitHub Actions run is red | Open the completed run for the revision you intend to verify. A later successful run does not change a historical run's result. |

**Returning after closing the terminal:** on Mac, open Terminal and run `bash`;
on Windows, open Ubuntu. Then run:

```bash
source "$HOME/.elan/env"
cd "$HOME/PolynomialDiophantineEquations-paper/sumsquares_revision"
```

If you used the `-2` folder name, substitute it in the path. For complete local
verification, also reactivate the environment created in D2:

```bash
source "$HOME/sumsquares-verification-venv/bin/activate"
```

To rebuild this package while retaining the dependency cache, run
`lake clean RequestProject`, then repeat the build block in B5 or C6.

### CI maintenance

The workflow runs on relevant pushes and pull requests and supports manual
runs. It checks the exact selected commit and records that commit in its logs
and artifact name. The Ubuntu 22.04 runner is scheduled to retire on
**17 April 2027**. Before that date, move CI to a supported runner on which the
same sandbox test and complete verifier succeed; see the
[official retirement notice](https://github.com/actions/runner-images/issues/14254).

## Provenance

The original formal proof development was assisted by
[Aristotle (Harmonic)](https://aristotle.harmonic.fun). The revision audit,
statement interface, packaging repairs and reproducibility checks were assisted
by ChatGPT. `formalization.yaml` records the scope, sources, automation, review
status and known differences between the paper's proofs and the Lean proofs.
