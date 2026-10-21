# Lean formalisation: "On the polynomial values represented by binary quadratic forms"

Lean 4 formalisation of the paper by B. Grechuk and J. Agbanwa (revision R1).
Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.

## Layout

| File | Content |
| --- | --- |
| `RequestProject/Main.lean` | The complete formal development: definitions, all results of the paper and their proofs (no `sorry`, no extra axioms). |
| `Challenge.lean` | Comparator challenge: every main result stated as a `theorem` with a `sorry` proof (namespace `Paper`), using only Mathlib and the four definitions `PolyQF.S2`, `PolyQF.Du`, `PolyQF.bqf`, `PolyQF.AdmissibleDegrees` (copied verbatim from `Main.lean`). Includes Propositions 2.1, 2.2, 4.1, 4.2, 4.3, Algorithms 2.1 and 4.1, Corollaries 3.1 and 3.2 and the "if and only if" criterion of the degenerate case. |
| `Solution.lean` | Comparator solution: the same statements, each proved by the corresponding theorem of `Main.lean`. |
| `comparator.json` | Configuration for the [comparator](https://github.com/leanprover/comparator) (`challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`, `enable_nanoda`). |
| `formalization.yaml` | Metadata (format version 0.4): paper, toolchain, files, and the correspondence between paper results and Lean theorems. |
| `verify.sh` | Builds everything, checks for `sorry`, runs an offline pre-check and then the comparator. |
| `scripts/CheckComparator.lean` | Offline pre-check, in Lean, of the comparator conditions (identical statements and definitions, permitted axioms only). |

## Verification

```bash
lake exe cache get        # download Mathlib build artefacts
lake build                # builds RequestProject, Challenge and Solution
COMPARATOR=/path/to/comparator ./verify.sh
```

The comparator additionally requires `landrun` and `lean4export` on `PATH`.
Without the comparator, `lake env lean --run scripts/CheckComparator.lean` performs the
same checks on the Lean side.

## Citing this formalisation

Both links in footnote b of the paper, and this README, should cite one and the same commit:
the commit that contains `RequestProject/Main.lean` together with `Challenge.lean`,
`Solution.lean`, `comparator.json` and `formalization.yaml`.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
