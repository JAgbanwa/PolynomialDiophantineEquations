# Project snapshot

This file records the immutable snapshots of the Lean formalization accompanying

> **On the polynomial values represented by quadratic forms**
> Bogdan Grechuk and Jamal Agbanwa (manuscript IJNT-D-26-00150)

Each snapshot is an annotated, immutable git tag. A tag is never moved or deleted: to
publish a correction, a new tag is added below. Citing a tag (or the commit it points at)
therefore pins the exact sources, the exact `lean-toolchain` and the exact
`lake-manifest.json` against which the proofs were checked.

## Current snapshot

| Field | Value |
| --- | --- |
| Tag | `snapshot-2026-09-06` |
| Manuscript version | revision of 6 September 2026 (Sections 1–4; the former Section 5, Conclusion, is deleted) |
| Lean toolchain | `leanprover/lean4:v4.28.0` |
| Mathlib | tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Compared declarations | the sixteen declarations listed in `comparator.json` |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |

Contents of this snapshot, relative to the previous state of the repository: the Lean
documentation is synchronized with the 6 September 2026 revision of the manuscript. In
particular

* the commentary on `prop_4_2` now records that the manuscript proves Proposition 4.2 by
  applying Gauss's theorem on integer points of conics, **[11, Proposition 3.14]**, to the
  conic `a x² + b x + c = −Δ(v₀ + 2mw)²` in the variables `(x, w)`, and that the Lean proof
  instead completes the square and uses the residue-controlled Pell theorem
  `genPell_infinite_cong`;
* the residue-controlled generalized Pell statement is no longer described as a lemma "of
  Section 2" of the manuscript. The revision states no such lemma: it quotes
  [11, Proposition 5.4] in the proof of Proposition 2.3 and [11, Proposition 3.14] in the
  proof of Proposition 4.2. Since a Lean development cannot cite the literature, those
  inputs are proved here, and `residue_controlled_pell` /
  `PolynomialValuesQuadraticForms.residue_controlled_pell_lemma` are documented as
  auxiliary results of the formalization that underlie the formal proofs of Propositions
  2.3 and 4.2;
* references to the deleted Section 5 are removed from `formalization.yaml`, `README.md`
  and the module documentation; the limitation for `y² + z² = x⁶ + 3`
  (`pow6_add3_algorithm_fails`) is attributed to Section 1, where the revision places it;
* the equation numbers quoted in the documentation follow the revision throughout — in
  Section 4 the auxiliary equation (29), the congruences (30), the solution formulas (31),
  the reduced form (32), the periodicity (33), the equations (34) with the families (35),
  (36), and the degenerate case (37), (38).

No statement and no proof was changed: the sixteen compared declarations, and every
theorem of `RequestProject/Main.lean`, are as in the previous state of the repository.

## Verifying a snapshot

```sh
git checkout snapshot-2026-09-06
lake exe cache get      # optional
lake build              # builds RequestProject, Challenge and Solution
./verify.sh             # runs the comparator on comparator.json
```

`Challenge.lean` contains one deliberate `sorry` per advertised statement, as the
comparator protocol requires; there is no `sorry`, `admit` or `axiom` anywhere else.
