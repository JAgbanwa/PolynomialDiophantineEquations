import Mathlib
/-!
# Arbitrarily large integer solutions of `z² + y²z + x³ - 2 = 0`
This file studies the Diophantine equation
  `z² + y² z + x³ - 2 = 0`,                                             (F)
the second equation of size `H = 22` in Table 5 of B. Grechuk, *A systematic
approach to Diophantine equations: open problems*.  For (F) both **Problem 2**
(does it have, for every `k`, a solution with `min(|x|, |y|, |z|) ≥ k`?) and
**Problem 4** (list all integer solutions or prove there are infinitely many)
are listed as open; (F) is also the first entry of Table 7 and of Table 12.
## What is proved here
Equation (F) says exactly that `z (z + y²) = 2 - x³`, so every factorisation of
`2 - x³` into two factors whose difference is a perfect square produces a
solution.  This is recorded in the two constructors `sol_of_factorisation_pos`
(for `x > 0`) and `sol_of_factorisation_neg` (for `x < 0`), and conversely every
solution arises this way (`factorisation_of_sol`).
Searching over all `x` with `|x| ≤ 10⁶` and all divisors of `x³ ∓ 2` gives
solutions in which `min(|x|, |y|, |z|)` is as large as the constant appearing in
`problem2_le` below.  Consequently Problem 2 for (F) has a positive answer for
every `k` up to that constant.  This is a *partial* result: Problem 2 for (F)
remains open, since it is not known whether `min(|x|, |y|, |z|)` is unbounded
along the solution set.
-/
namespace Table5Cubic
/-! ## The factorisation form of the equation -/
/-- Equation (F) is equivalent to `z (z + y²) = 2 - x³`. -/
theorem eq_iff_factorisation (x y z : ℤ) :
    z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0 ↔ z * (z + y ^ 2) = 2 - x ^ 3 := by
  constructor <;> intro h <;> linear_combination h
/-- **Constructor, `x > 0` branch.**  If `c d = x³ - 2` and `y² = c + d`, then
`(x, y, -c)` is a solution of (F). -/
theorem sol_of_factorisation_pos (x y c d : ℤ) (h : c * d = x ^ 3 - 2)
    (hy : y ^ 2 = c + d) :
    (-c) ^ 2 + y ^ 2 * (-c) + x ^ 3 - 2 = 0 := by
  rw [hy]; linear_combination -h
/-- **Constructor, `x < 0` branch.**  If `d e = (-x)³ + 2` and `y² = e - d`, then
both `(x, y, d)` and `(x, y, -e)` are solutions of (F). -/
theorem sol_of_factorisation_neg (n y d e : ℤ) (h : d * e = n ^ 3 + 2)
    (hy : y ^ 2 = e - d) :
    d ^ 2 + y ^ 2 * d + (-n) ^ 3 - 2 = 0 ∧ (-e) ^ 2 + y ^ 2 * (-e) + (-n) ^ 3 - 2 = 0 := by
  constructor
  · rw [hy]; linear_combination h
  · rw [hy]; linear_combination h
/-- Conversely, every solution of (F) gives a factorisation of `2 - x³` into two
factors differing by the square `y²`. -/
theorem factorisation_of_sol (x y z : ℤ) (h : z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0) :
    z * (z + y ^ 2) = 2 - x ^ 3 ∧ (z + y ^ 2) - z = y ^ 2 := by
  refine ⟨by linear_combination h, by ring⟩
/-! ## Quantitative form of Problem 2 for (F) -/
/-- **A sufficient criterion for a positive answer to Problem 2 for (F).**
If, for every `k`, there is an `n ≥ k` such that `n³ - 2` admits a factorisation
`n³ - 2 = c d` with `c ≥ k` and `c + d` a square `y²` with `y ≥ k`, then (F) has
solutions with `min(|x|, |y|, |z|) ≥ k` for every `k`.
This isolates what is missing for Problem 2: computer search produces such data for
many `n` (see `problem2_le`), but no proof that they exist for every `k` is known. -/
theorem problem2_of_unbounded_factorisations
    (H : ∀ k : ℤ, ∃ n c d y : ℤ, k ≤ n ∧ k ≤ c ∧ k ≤ y ∧ c * d = n ^ 3 - 2 ∧ y ^ 2 = c + d) :
    ∀ k : ℤ, ∃ x y z : ℤ, z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  intro k
  obtain ⟨n, c, d, y, hn, hc, hy, hcd, hsq⟩ := H k
  refine ⟨n, y, -c, sol_of_factorisation_pos n y c d hcd hsq, ?_, ?_, ?_⟩
  · exact hn.trans (le_abs_self n)
  · exact hy.trans (le_abs_self y)
  · rw [abs_neg]; exact hc.trans (le_abs_self c)
/-- **Quantitative form of Problem 2 for `z² + y²z + x³ - 2 = 0`.**
For every `k ≤ 558452` the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`.  The witness `(x, y, z) = (-558452, 567081, -321581402146)`
comes from the factorisation `558452³ + 2 = 541585 · 321581402146` of `(-x)³ + 2`, whose
two factors differ by `567081²`. -/
theorem problem2_le {k : ℤ} (hk : k ≤ 558452) :
    ∃ x y z : ℤ, z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  refine ⟨-558452, 567081, -321581402146, by norm_num, ?_, ?_, ?_⟩
  · rw [show |(-558452 : ℤ)| = 558452 by norm_num]; exact hk
  · rw [show |(567081 : ℤ)| = 567081 by norm_num]; linarith
  · rw [show |(-321581402146 : ℤ)| = 321581402146 by norm_num]; linarith
end Table5Cubic
