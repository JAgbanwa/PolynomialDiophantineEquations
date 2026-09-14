This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```


# Summary of changes for run 9c91ab06-cf21-425c-89ed-37363690c2f1
Fixed the three reported issues in `RequestProject/Main.lean`, all of which came from deprecations/linting in newer Mathlib versions:

- `mvTwoEquiv_X0` and `mvTwoEquiv_X1`: the `simp only` calls relied on the now-deprecated `AlgEquiv.toRingEquiv_eq_coe` and carried arguments that are no longer needed. Both proofs were rewritten to short, version-robust proofs that no longer mention any deprecated lemma: `mvTwoEquiv_X0` supplies the `finSuccEquiv` evaluation at `X 1` as an explicit `have` (avoiding the looping `1 = Fin.succ 0` rewrite) and `mvTwoEquiv_X1` uses `MvPolynomial.finSuccEquiv_X_zero`.
- `integer_solutions_finite`: the step that used the deprecated `Set.mem_setOf_eq` now states the cast solution equation directly as a `have` and closes the membership goal by `exact`, so no set-membership simp lemma is needed.

The file builds cleanly with no errors, no warnings, and no `sorry`; all previously proved statements (irreducibility, smoothness, and the finiteness results) are unchanged and still verified. The work is committed.

# Summary of changes for run 87f6876d-230d-4146-beb7-0ad197ddbb11
**Verdict on the paper: its mathematics is correct.** The equation x⁴ + xy + y³ + 1 = 0 really does have only finitely many rational (hence integer) solutions, and the paper's proof is sound: every algebraic computation checks out, and its two external inputs (the genus formula for a smooth plane curve, and Faltings' theorem) are genuine theorems applied to a situation whose hypotheses the paper verifies. So the "infinitude" claim it rebuts is indeed false. The one caveat, which the paper itself states, is that the argument is not self-contained: it gives no height bound and no complete list of solutions, and it depends on Faltings' theorem.

**Formalization.** The whole paper is formalized in the single file `RequestProject/Main.lean`, which builds cleanly with no `sorry` and no extra axioms (only `propext`, `Classical.choice`, `Quot.sound`). Its contents:

- *Section 2 (geometric irreducibility)*, proved unconditionally: `no_poly_root` (the degree argument showing s³ + x·s + x⁴ + 1 ≠ 0 for every s ∈ ℂ[x]), `no_ratfunc_root` (no root in ℂ(x), via integral closedness of ℂ[x]), `cubicInY_irreducible` (Gauss' lemma plus the "a cubic without roots is irreducible" criterion), and finally `quartic_irreducible`: x⁴ + xy + y³ + 1 is irreducible in ℂ[x,y].
- *Section 3 (smoothness)*, proved unconditionally: `no_affine_singular_point` rules out affine complex singularities — the paper's absolute-value contradiction is replaced by the equivalent purely algebraic one (x⁴ = 3/5, x⁵ = −1/48 are incompatible) — and `quarticForm_smooth` shows the projective quartic X⁴ + XYZ² + Y³Z + Z⁴ has no singular point at all, including the point at infinity [0 : 1 : 0]. Homogeneity of degree 4 (`quarticForm_isHomogeneous`) and the dehomogenization identity are also proved.
- *Section 4 (conclusion)*: since neither Faltings' theorem nor the plane-curve genus formula exists in Mathlib, they are packaged into one explicit, general hypothesis `FaltingsSmoothPlaneCurves` (a smooth plane curve of degree ≥ 4 over ℚ with geometrically irreducible affine equation has finitely many rational points in the affine chart) — mirroring the paper's own use of them as black boxes. Granting it, `rational_solutions_finite` gives Theorem 1, `integer_solutions_finite` and `not_infinite_integer_solutions` give the integer statement, and all of that hypothesis's side conditions are discharged unconditionally by the results above. The two explicit solutions (0, −1) and (1, −1) are verified in `solution_zero` and `solution_one`.
