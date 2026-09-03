This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# On the polynomial values represented by quadratic forms — Lean formalization

Lean 4 formalization of the paper

> **On the polynomial values represented by quadratic forms**
> Bogdan Grechuk and Jamal Agbanwa [\[1\]](https://arxiv.org/pdf/2607.06627)

The development proves, with no `sorry` and no added `axiom`, that `x⁶ − 4` is a sum of
two squares for infinitely many integers `x`, and hence that the Diophantine equation
`y² + x³y + z² + 1 = 0` has infinitely many integer solutions (Proposition 3.1), together
with the four further length-9 equations of Proposition 3.2, the general theory of
Section 4 (Propositions 4.1, 4.2, 4.4, Algorithms 2.2 and 4.3, non-multiplicativity of
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
sandbox, checks that the ten compared declarations have exactly the statements advertised
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

## Differences from the paper's proofs

The formalized statements are the paper's statements. Two proofs are organised
differently, and this is documented in the module docstring of
`RequestProject/Main.lean`, at the declarations concerned, and in
`formalization.yaml` under `fidelity.divergences`:

* **Proposition 4.2** is proved via a residue-controlled Pell theorem
  (`genPell_infinite_cong`), rather than via Gauss's theorem applied to the conic (31).
  The Lean statement also records that the non-degeneracy assumption `Δ ≠ 0` is not
  needed for Proposition 4.2 itself.
* **Proposition 4.4** is verified directly from the explicit polynomial families given in
  the paper (by `ring`), rather than by re-running the tangent construction.

In addition, Gauss's theorem on generalised Pell equations, quoted in the paper from
[9, Proposition 5.4], is proved from scratch here rather than assumed.

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
