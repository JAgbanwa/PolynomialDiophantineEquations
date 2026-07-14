import Mathlib
/-!
# The Diophantine equation `z² + y²·z + x³ − 2 = 0`
This file formalises the paper
  *An exact divisor parametrisation for the integer solutions of `z² + y²z + x³ − 2 = 0`*
  (J. Agbanwa),
which gives a complete elementary classification of the integer solutions of
  `z² + y²·z + x³ − 2 = 0,   x, y, z ∈ ℤ.`
## What the paper actually proves
The paper proves a **complete divisor parametrisation** of the solution set (its
Theorems 1 and 2), together with the supporting lemmas and two corollaries.  All of these
statements are formalised and proved below:
* `z_ne_zero`        — Lemma 3: every solution has `z ≠ 0`.
* `factorisation`    — Lemma 4: the equation is equivalent to `z·(z + y²) = 2 − x³`.
* `divisor_criterion`— Lemma 5 / Theorem 1: the divisor–square criterion.
* `factor_pair`      — Theorem 2: the factor-pair (`a·b = 2 − x³`, `b − a = y²`) form.
* `sign_symmetry`    — Corollary 6: `y ↦ −y` is a symmetry.
* `sign_restriction` — Corollary 7: for `x ≥ 2` every solution has `z < 0 < z + y²`,
                        so in particular `y ≠ 0`.
* `sol_ex1`–`sol_ex3`— explicit sample solutions from the paper's table.
## On the "infinitude" question
The user's prompt describes the paper as proving *the infinitude of integer solutions*.
This is a misreading: the paper does **not** claim or prove that there are infinitely many
solutions.  What it proves is a *complete parametrisation*, which, for each fixed `x`, yields
a **finite** list of solutions (`2 − x³` is a non-zero integer, hence has finitely many
divisors `z`).  So infinitude is not a consequence of the paper's results.
Whether the full solution set is infinite is a genuinely harder question and is **not**
settled here.  Structurally the affine surface `z² + y²z + x³ = 2` is fibred by genus-one
curves (fixing any one of `x`, `y`, `z` leaves an elliptic curve, which by Siegel's theorem
has only finitely many integer points), and its only obvious symmetries are the two
order-two maps `y ↦ −y` (`sign_symmetry`) and the Vieta involution `z ↦ −y² − z`
(`vieta` below).  None of these produce an infinite family, so infinitude does not follow by
any elementary argument, and we do not assert it.
-/
open scoped Classical
/-- The Diophantine equation `z² + y²·z + x³ − 2 = 0` studied in the paper. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0
/-- **Lemma 3.** No integer cube equals `2`, hence every solution has `z ≠ 0`. -/
theorem z_ne_zero (x y z : ℤ) (h : IsSol x y z) : z ≠ 0 := by
  rintro rfl
  simp only [IsSol] at h
  have hx : x ^ 3 = 2 := by ring_nf at h ⊢; linarith
  rcases (by omega : x ≤ 1 ∨ 2 ≤ x) with h1 | h1
  · nlinarith [hx, sq_nonneg (2 * x + 1)]
  · nlinarith [hx, sq_nonneg x]
/-- **Lemma 4 (fundamental factorisation).** The equation is equivalent to
`z·(z + y²) = 2 − x³`. -/
theorem factorisation (x y z : ℤ) : IsSol x y z ↔ z * (z + y ^ 2) = 2 - x ^ 3 := by
  unfold IsSol; constructor <;> intro h <;> nlinarith [h]
/-- **Lemma 5 / Theorem 1 (divisor–square criterion).** A triple `(x, y, z)` is a solution
iff `z ≠ 0`, `z` divides `2 − x³` with cofactor `q`, and `y²` equals `q − z` (equivalently
`y² = (2 − x³)/z − z`, which is automatically a non-negative square, being `y²`). -/
theorem divisor_criterion (x y z : ℤ) :
    IsSol x y z ↔ z ≠ 0 ∧ ∃ q : ℤ, 2 - x ^ 3 = z * q ∧ y ^ 2 = q - z := by
  constructor
  · intro h
    refine ⟨z_ne_zero x y z h, z + y ^ 2, ?_, by ring⟩
    have := (factorisation x y z).1 h; linarith [this]
  · rintro ⟨_, q, hq, hy⟩
    rw [factorisation]
    have hq2 : q = z + y ^ 2 := by linarith
    rw [hq2] at hq; linarith
/-- **Theorem 2 (factor-pair form).** A triple `(x, y, z)` is a solution iff there is a factor
pair `(a, b)` of `2 − x³` with `a = z`, `b = z + y²`, `a ≠ 0`, and difference `b − a = y²`. -/
theorem factor_pair (x y z : ℤ) :
    IsSol x y z ↔
      ∃ a b : ℤ, a = z ∧ b = z + y ^ 2 ∧ a * b = 2 - x ^ 3 ∧ b - a = y ^ 2 ∧ a ≠ 0 := by
  constructor
  · intro h
    exact ⟨z, z + y ^ 2, rfl, rfl, (factorisation x y z).1 h, by ring, z_ne_zero x y z h⟩
  · rintro ⟨a, b, ha, hb, hab, _, _⟩
    subst ha hb; rw [factorisation]; linarith
/-- **Corollary 6 (sign symmetry in `y`).** Replacing `y` by `−y` sends solutions to
solutions. -/
theorem sign_symmetry (x y z : ℤ) (h : IsSol x y z) : IsSol x (-y) z := by
  unfold IsSol at *; ring_nf at *; linarith
/-- **Corollary 7 (sign restriction for `x ≥ 2`).** If `x ≥ 2` then any solution satisfies
`z < 0 < z + y²`; in particular `y ≠ 0`. -/
theorem sign_restriction (x y z : ℤ) (hx : 2 ≤ x) (h : IsSol x y z) :
    z < 0 ∧ 0 < z + y ^ 2 ∧ y ≠ 0 := by
  have hf := (factorisation x y z).1 h
  have hneg : z * (z + y ^ 2) < 0 := by nlinarith [hx, sq_nonneg x]
  have hy2 : (0 : ℤ) ≤ y ^ 2 := sq_nonneg y
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hneg, hy2]
  · nlinarith [hneg, hy2]
  · rintro rfl; simp at hneg; nlinarith [hneg]
/-- The **Vieta involution**: viewing the equation as a quadratic in `z`, the two roots are
`z` and `−y² − z`, so `(x, y, −y² − z)` is again a solution.  This is one of the two order-two
symmetries of the equation (the other being `sign_symmetry`); together they do not generate an
infinite family. -/
theorem vieta (x y z : ℤ) (h : IsSol x y z) : IsSol x y (-(y ^ 2) - z) := by
  unfold IsSol at *; ring_nf at *; nlinarith [h]
/-- Applying the Vieta involution twice returns the original solution. -/
theorem vieta_involutive (y z : ℤ) : (-(y ^ 2) - (-(y ^ 2) - z)) = z := by ring
/-! ### Explicit sample solutions from the paper's table -/
/-- `(8, 7, −15)` is a solution (paper's table, `x = 8`). -/
theorem sol_ex1 : IsSol 8 7 (-15) := by unfold IsSol; norm_num
/-- `(26, 19, −58)` is a solution (paper's verification certificate, §4). -/
theorem sol_ex2 : IsSol 26 19 (-58) := by unfold IsSol; norm_num
/-- `(-2, 3, 1)` is a solution (paper's table, `x = -2`). -/
theorem sol_ex3 : IsSol (-2) 3 1 := by unfold IsSol; norm_num
/-- The solution set is non-empty. -/
theorem sol_nonempty : ∃ x y z : ℤ, IsSol x y z := ⟨8, 7, -15, sol_ex1⟩
