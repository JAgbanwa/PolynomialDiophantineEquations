# On the polynomial values represented by quadratic forms — Lean formalization

This Lake project formalizes the results listed below from *On the polynomial values
represented by quadratic forms* by Bogdan Grechuk and Jamal Agbanwa
([arXiv:2607.06627](https://arxiv.org/abs/2607.06627)). It includes the proof that
`x⁶ − 4` is a sum of two squares for infinitely many integers `x`, the five
Diophantine equations of Corollaries 3.1 and 3.2 with infinitely many integer solutions,
and results about general
binary quadratic forms.

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

Install Git, curl, Bash, Python 3, and
[Elan](https://github.com/leanprover/elan#installation). Elan selects and downloads the
version in `lean-toolchain` when `lean` or `lake` is invoked from this project.

The audit also uses standard Unix utilities, including `find`, `sort`, `mktemp`, and
`grep` with the word-boundary expressions supported by GNU grep. CI provides a tested
Ubuntu 24.04 environment. When running the audit on another platform, provide these
utilities and Python as `python3`.

## Build the current checkout

From a fresh clone:

```bash
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git
cd PolynomialDiophantineEquations/sumsquares_revised
lean --version
python3 --version
lake exe cache get
lake build
bash verify.sh
```

`lean --version` must report `4.28.0`. The cache command downloads compiled Mathlib
artifacts to avoid rebuilding the dependencies from source. `lake build` builds all
three default targets, including `Challenge`.

A successful build prints `Build completed successfully`. A successful full audit ends
with `ALL CHECKS PASSED` and exits with status `0`. `bash verify.sh` includes its own
build, so it can also be used as the single build-and-audit command after fetching the cache.

### What the audit checks

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

To reproduce the successful run linked above, use a separate clone and select its
exact source commit:

```bash
git clone https://github.com/JAgbanwa/PolynomialDiophantineEquations.git PolynomialDiophantineEquations-verified
cd PolynomialDiophantineEquations-verified
git checkout --detach 00743362664f95bc747ad9d960499094de7293eb
cd sumsquares_revised
lake exe cache get
bash verify.sh
git rev-parse HEAD
```

The final command must print `00743362664f95bc747ad9d960499094de7293eb`.
The checkout is intentionally detached. Immutable references for this snapshot are:

- [Project folder](https://github.com/JAgbanwa/PolynomialDiophantineEquations/tree/00743362664f95bc747ad9d960499094de7293eb/sumsquares_revised)
- [Main proof file](https://github.com/JAgbanwa/PolynomialDiophantineEquations/blob/00743362664f95bc747ad9d960499094de7293eb/sumsquares_revised/RequestProject/Main.lean)

## Credits and licence

The project acknowledges [Aristotle](https://aristotle.harmonic.fun) (Harmonic) for work
on the Lean proofs. The repository currently has no `LICENSE` file; a project licence
has not been recorded.
