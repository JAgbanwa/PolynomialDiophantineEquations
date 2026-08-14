import Mathlib
/-!
# Arbitrarily large integer solutions of `y² + x²y + z²x - 2 = 0`
This file studies the Diophantine equation
  `y² + x² y + z² x - 2 = 0`,                                          (E)
which is one of the two equations of size `H = 22` listed in Table 5 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*,
as an equation for which **Problem 2** is open.  Problem 2 asks whether, for
every `k ≥ 0`, the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`.
## What is proved here
Fix `x = -m` with `m > 0`.  Completing the square in `y` shows that (E) is
solvable with `x = -m` exactly when the Pell-type equation
`w² - 4 m z² = m⁴ + 8` is solvable (`pell_iff`).  Whenever it is solvable and
`4m` is not a perfect square, multiplying by units of the Pell equation
`T² - 4 m U² = 1` produces *infinitely many* solutions of (E) with this fixed
`x = -m` and with `|y|, |z| → ∞`.  This is made completely explicit by the
step map of `table5_step`, which needs no irrationality input at all: it only
needs one solution `s² + s = m U²` of the Pell equation, written in terms of
`T = 2s + 1`.
Consequently, for every `m` admitting a base solution, all of `|x| = m`,
`|y|` and `|z|` can be made `≥ k` for every `k ≤ m` (`problem2_of_base`).
Base solutions were found by computer search for
`m = 17, 31, 71, 79, 97, 142, 193, 199, 241, …, 4591, …, 2272969, 10560367, …, 448636753`;
the largest one used here is `m = 448636753`, giving `problem2_le_448636753`.
This is a *partial* result: Problem 2 for (E) remains open, since it is not
known whether the set of `m` admitting a base solution is unbounded.
-/
namespace Table5
/-! ## Reduction to a Pell equation -/
/-- For `x = -m`, equation (E) is solvable if and only if the Pell-type
equation `w² - 4 m z² = m⁴ + 8` is solvable. -/
theorem pell_iff (m : ℤ) :
    (∃ y z : ℤ, y ^ 2 + (-m) ^ 2 * y + z ^ 2 * (-m) - 2 = 0) ↔
      (∃ w z : ℤ, w ^ 2 - 4 * m * z ^ 2 = m ^ 4 + 8) := by
  constructor
  · rintro ⟨y, z, h⟩
    exact ⟨2 * y + m ^ 2, z, by linear_combination 4 * h⟩
  · rintro ⟨w, z, h⟩
    -- `w` and `m²` have the same parity, so `y := (w - m²)/2` is an integer
    have hev : Even (w - m ^ 2) := by
      have hprod : Even ((w - m ^ 2) * (w + m ^ 2)) := by
        refine ⟨4 + 2 * m * z ^ 2, ?_⟩
        linear_combination h
      rcases Int.even_mul.mp hprod with h1 | h1
      · exact h1
      · obtain ⟨a, ha⟩ := h1
        exact ⟨a - m ^ 2, by linarith⟩
    obtain ⟨y, hy⟩ := hev
    refine ⟨y, z, ?_⟩
    have hw : w = 2 * y + m ^ 2 := by linarith
    subst hw
    have h4 : 4 * (y ^ 2 + (-m) ^ 2 * y + z ^ 2 * (-m) - 2) = 0 := by linear_combination h
    linarith
/-! ## The step map -/
/-- **Step map.**  If `s² + s = m U²` (equivalently `T² - 4mU² = 1` for
`T = 2s+1`), then the map
`(y, z) ↦ ((2s+1)y + 2mUz + m²s, 2Uy + (2s+1)z + m²U)`
sends solutions of `y² + m²y - m z² - 2 = 0` to solutions of the same
equation. -/
theorem table5_step (m s U y z : ℤ) (hs : s ^ 2 + s = m * U ^ 2)
    (h : y ^ 2 + m ^ 2 * y - m * z ^ 2 - 2 = 0) :
    ((2 * s + 1) * y + 2 * m * U * z + m ^ 2 * s) ^ 2
        + m ^ 2 * ((2 * s + 1) * y + 2 * m * U * z + m ^ 2 * s)
        - m * (2 * U * y + (2 * s + 1) * z + m ^ 2 * U) ^ 2 - 2 = 0 := by
  linear_combination (4 * y ^ 2 - 4 * m * z ^ 2 + 4 * m ^ 2 * y + m ^ 4) * hs + h
/-- The iterated step map, as a sequence of pairs `(yₙ, zₙ)`. -/
def seqPair (m s U y0 z0 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (y0, z0)
  | n + 1 =>
      let p := seqPair m s U y0 z0 n
      ((2 * s + 1) * p.1 + 2 * m * U * p.2 + m ^ 2 * s,
        2 * U * p.1 + (2 * s + 1) * p.2 + m ^ 2 * U)
/-- Every term of the sequence solves the equation. -/
theorem seqPair_sol (m s U y0 z0 : ℤ) (hs : s ^ 2 + s = m * U ^ 2)
    (h0 : y0 ^ 2 + m ^ 2 * y0 - m * z0 ^ 2 - 2 = 0) :
    ∀ n : ℕ, ((seqPair m s U y0 z0 n).1) ^ 2 + m ^ 2 * ((seqPair m s U y0 z0 n).1)
        - m * ((seqPair m s U y0 z0 n).2) ^ 2 - 2 = 0 := by
  intro n
  induction n with
  | zero => simpa [seqPair] using h0
  | succ n ih => simpa [seqPair] using table5_step m s U _ _ hs ih
/-- Under positivity assumptions both components grow at least linearly. -/
theorem seqPair_ge (m s U y0 z0 : ℤ) (hm : 1 ≤ m) (hU : 1 ≤ U) (hs1 : 1 ≤ s)
    (hy0 : 0 ≤ y0) (hz0 : 0 ≤ z0) :
    ∀ n : ℕ, (n : ℤ) ≤ (seqPair m s U y0 z0 n).1 ∧
      (n : ℤ) ≤ (seqPair m s U y0 z0 n).2 := by
  intro n
  induction n with
  | zero => simpa [seqPair] using ⟨hy0, hz0⟩
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      have hy : (0 : ℤ) ≤ (seqPair m s U y0 z0 n).1 := le_trans hn h1
      have hz : (0 : ℤ) ≤ (seqPair m s U y0 z0 n).2 := le_trans hn h2
      have hm2 : (1 : ℤ) ≤ m ^ 2 := by nlinarith
      have hms : (1 : ℤ) ≤ m ^ 2 * s := by nlinarith
      have hmU : (1 : ℤ) ≤ m ^ 2 * U := by nlinarith
      have hsy : (0 : ℤ) ≤ 2 * s * (seqPair m s U y0 z0 n).1 :=
        mul_nonneg (by linarith) hy
      have hsz : (0 : ℤ) ≤ 2 * s * (seqPair m s U y0 z0 n).2 :=
        mul_nonneg (by linarith) hz
      have hmuz : (0 : ℤ) ≤ 2 * m * U * (seqPair m s U y0 z0 n).2 :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz
      have huy : (0 : ℤ) ≤ 2 * U * (seqPair m s U y0 z0 n).1 :=
        mul_nonneg (by linarith) hy
      constructor
      · show ((n : ℕ) + 1 : ℤ) ≤ _
        simp only [seqPair]
        nlinarith
      · show ((n : ℕ) + 1 : ℤ) ≤ _
        simp only [seqPair]
        nlinarith
/-! ## Arbitrarily large solutions for a fixed `x = -m` -/
/-- **Main construction.**  From one solution of the Pell equation
`s² + s = m U²` (with `s, U ≥ 1`) and one nonnegative base solution of (E)
with `x = -m`, one obtains solutions of (E) with `x = -m` and with `y` and `z`
arbitrarily large. -/
theorem exists_large_yz (m s U y0 z0 : ℤ) (hm : 1 ≤ m) (hU : 1 ≤ U) (hs1 : 1 ≤ s)
    (hs : s ^ 2 + s = m * U ^ 2) (hy0 : 0 ≤ y0) (hz0 : 0 ≤ z0)
    (h0 : y0 ^ 2 + m ^ 2 * y0 - m * z0 ^ 2 - 2 = 0) (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧ y ^ 2 + (-m) ^ 2 * y + z ^ 2 * (-m) - 2 = 0 := by
  obtain ⟨h1, h2⟩ := seqPair_ge m s U y0 z0 hm hU hs1 hy0 hz0 N.toNat
  have hN : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  refine ⟨(seqPair m s U y0 z0 N.toNat).1, (seqPair m s U y0 z0 N.toNat).2,
    le_trans hN h1, le_trans hN h2, ?_⟩
  have := seqPair_sol m s U y0 z0 hs h0 N.toNat
  linarith [this]
/-! ## Removing the need for an explicit Pell unit -/
/-- The two roots of (E) in `y` for fixed `x = -m`, `z`: if `y` is a solution then so
is `-m² - y`. -/
theorem table5_flip (m y z : ℤ) (h : y ^ 2 + m ^ 2 * y - m * z ^ 2 - 2 = 0) :
    (-m ^ 2 - y) ^ 2 + m ^ 2 * (-m ^ 2 - y) - m * z ^ 2 - 2 = 0 := by
  linear_combination h
/-- **Nonemptiness implies unboundedness.**  If `m ≥ 1`, `4m` is not a perfect square,
and equation (E) has *one* integer solution with `x = -m`, then it has solutions with
`x = -m` and with `y`, `z` arbitrarily large. -/
theorem large_of_base (m y0 z0 : ℤ) (hm : 1 ≤ m) (hsq : ¬ IsSquare (4 * m))
    (h0 : y0 ^ 2 + m ^ 2 * y0 - m * z0 ^ 2 - 2 = 0) (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧ y ^ 2 + (-m) ^ 2 * y + z ^ 2 * (-m) - 2 = 0 := by
  -- a solution of the Pell equation `T² - 4m U² = 1`
  obtain ⟨T, U, hTU, hU0⟩ := Pell.exists_of_not_isSquare (by linarith : (0:ℤ) < 4 * m) hsq
  have hTU' : |T| ^ 2 - 4 * m * |U| ^ 2 = 1 := by
    rw [sq_abs, sq_abs]; exact hTU
  have hU1 : 1 ≤ |U| := by
    rcases lt_or_eq_of_le (abs_nonneg U) with h | h
    · omega
    · exact absurd (abs_eq_zero.mp h.symm) hU0
  have hTpos : 0 ≤ |T| := abs_nonneg T
  have hT3 : 3 ≤ |T| := by nlinarith
  -- `|T|` is odd, say `|T| = 2s + 1`
  obtain ⟨s, hs2⟩ : ∃ s : ℤ, |T| = 2 * s + 1 := by
    rcases Int.even_or_odd |T| with ⟨a, ha⟩ | ⟨a, ha⟩
    · exfalso
      have h4 : 4 * (a ^ 2 - m * |U| ^ 2) = 1 := by rw [ha] at hTU'; linarith [hTU']
      omega
    · exact ⟨a, ha⟩
  have hs1 : 1 ≤ s := by omega
  have hs : s ^ 2 + s = m * |U| ^ 2 := by
    rw [hs2] at hTU'; linarith [hTU']
  -- normalise the base solution to have `y ≥ 0` and `z ≥ 0`
  have hz0 : (0 : ℤ) ≤ |z0| := abs_nonneg z0
  have h0' : y0 ^ 2 + m ^ 2 * y0 - m * |z0| ^ 2 - 2 = 0 := by rw [sq_abs]; exact h0
  rcases le_or_gt 0 y0 with hy0 | hy0
  · exact exists_large_yz m s |U| y0 |z0| hm hU1 hs1 hs hy0 hz0 h0' N
  · have hpos : y0 + m ^ 2 < 0 := by nlinarith [sq_nonneg z0, sq_nonneg m]
    refine exists_large_yz m s |U| (-m ^ 2 - y0) |z0| hm hU1 hs1 hs (by linarith) hz0 ?_ N
    exact table5_flip m y0 |z0| h0'
/-- For every `m ≥ 1` such that `4m` is not a perfect square and equation (E) has an
integer solution with `x = -m`, equation (E) has solutions with
`min(|x|, |y|, |z|) ≥ k` for every `k ≤ m`. -/
theorem problem2_of_base (m y0 z0 : ℤ) (hm : 1 ≤ m) (hsq : ¬ IsSquare (4 * m))
    (h0 : y0 ^ 2 + m ^ 2 * y0 - m * z0 ^ 2 - 2 = 0) {k : ℤ} (hk : k ≤ m) :
    ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  obtain ⟨y, z, hy, hz, heq⟩ := large_of_base m y0 z0 hm hsq h0 k
  refine ⟨-m, y, z, heq, ?_, ?_, ?_⟩
  · rw [abs_of_nonpos (by linarith)]; simpa using hk
  · exact le_trans hy (le_abs_self y)
  · exact le_trans hz (le_abs_self z)
/-- **A sufficient criterion for a positive answer to Problem 2 for (E).**
If there are arbitrarily large `m` with `4m` not a perfect square for which (E) has an
integer solution with `x = -m`, then (E) has solutions with `min(|x|, |y|, |z|) ≥ k`
for every `k`, i.e. Problem 2 for (E) has a positive answer.
This isolates exactly what is missing: computer search finds such `m`
(`m = 17, 31, 71, 79, 97, 142, 193, 199, 241, 433, 487, 553, 622, 823, 1241, 1246,
1297, 1351, 1423, 1609, 1801, 4591, …`), but no proof that they are unbounded is known. -/
theorem problem2_of_unbounded_good
    (H : ∀ k : ℤ, ∃ m y z : ℤ, k ≤ m ∧ ¬ IsSquare (4 * m) ∧
      y ^ 2 + m ^ 2 * y - m * z ^ 2 - 2 = 0) :
    ∀ k : ℤ, ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  intro k
  obtain ⟨m, y0, z0, hkm, hsq, h0⟩ := H (max k 1)
  exact problem2_of_base m y0 z0 (le_trans (le_max_right k 1) hkm) hsq h0
    (le_trans (le_max_left k 1) hkm)
/-! ## Explicit instances -/
/-- A convenient criterion for an integer to be a non-square. -/
theorem not_isSquare_of_between (n a : ℤ) (ha : 0 ≤ a) (h1 : a ^ 2 < n) (h2 : n < (a + 1) ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hr' : n = |r| ^ 2 := by rw [sq_abs, hr]; ring
  have h0 : 0 ≤ |r| := abs_nonneg r
  rcases le_or_gt |r| a with h | h
  · nlinarith
  · have h' : a + 1 ≤ |r| := by omega
    nlinarith
/-- For `x = -17` equation (E) has solutions with `y` and `z` arbitrarily large.
(Base solution `(y, z) = (142, 60)`.) -/
theorem large_solutions_x_neg_17 (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧ y ^ 2 + (-17 : ℤ) ^ 2 * y + z ^ 2 * (-17) - 2 = 0 :=
  large_of_base 17 142 60 (by norm_num)
    (by simpa using not_isSquare_of_between 68 8 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) N
/-- For `x = -4591` equation (E) has solutions with `y` and `z` arbitrarily large.
(Base solution `(y, z) = (15002, 8302)`.) -/
theorem large_solutions_x_neg_4591 (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧ y ^ 2 + (-4591 : ℤ) ^ 2 * y + z ^ 2 * (-4591) - 2 = 0 :=
  large_of_base 4591 15002 8302 (by norm_num)
    (by simpa using not_isSquare_of_between 18364 135 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) N
/-- **Quantitative form of Problem 2 for `y² + x²y + z²x - 2 = 0`.**
For every `k ≤ 4591` the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`. -/
theorem problem2_le_4591 {k : ℤ} (hk : k ≤ 4591) :
    ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| :=
  problem2_of_base 4591 15002 8302 (by norm_num)
    (by simpa using not_isSquare_of_between 18364 135 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) hk
/-- For `x = -670481` equation (E) has solutions with `y` and `z` arbitrarily large.
The base solution is `(y, z) = (-640725722543, 427430148)`; it was found by searching the
family `m = 2w² - 1` (here `w = 579`), for which `2w` is a square root of `2` modulo `m`. -/
theorem large_solutions_x_neg_670481 (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧
      y ^ 2 + (-670481 : ℤ) ^ 2 * y + z ^ 2 * (-670481) - 2 = 0 :=
  large_of_base 670481 (-640725722543) 427430148 (by norm_num)
    (by simpa using not_isSquare_of_between 2681924 1637 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) N
/-- **Quantitative form of Problem 2 for `y² + x²y + z²x - 2 = 0`.**
For every `k ≤ 670481` the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`.  (Sharper version of `problem2_le_4591`.) -/
theorem problem2_le_670481 {k : ℤ} (hk : k ≤ 670481) :
    ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| :=
  problem2_of_base 670481 (-640725722543) 427430148 (by norm_num)
    (by simpa using not_isSquare_of_between 2681924 1637 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) hk
/-- For `x = -10560367` equation (E) has solutions with `y` and `z` arbitrarily large.
The base solution is `(y, z) = (22373886, 15371288)`; it was found by a search over all
`y ≤ 6·10⁷` and all divisors `m` of `y² - 2` (the equation with `x = -m` is solvable with a
given `y` exactly when `m ∣ y² - 2` and `m y + (y² - 2)/m` is a perfect square). -/
theorem large_solutions_x_neg_10560367 (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧
      y ^ 2 + (-10560367 : ℤ) ^ 2 * y + z ^ 2 * (-10560367) - 2 = 0 :=
  large_of_base 10560367 22373886 15371288 (by norm_num)
    (by simpa using not_isSquare_of_between 42241468 6499 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) N
/-- **Quantitative form of Problem 2 for `y² + x²y + z²x - 2 = 0`.**
For every `k ≤ 10560367` the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`.  (Sharper version of `problem2_le_670481`.) -/
theorem problem2_le_10560367 {k : ℤ} (hk : k ≤ 10560367) :
    ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| :=
  problem2_of_base 10560367 22373886 15371288 (by norm_num)
    (by simpa using not_isSquare_of_between 42241468 6499 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) hk
/-- For `x = -448636753` equation (E) has solutions with `y` and `z` arbitrarily large.
The base solution is `(y, z) = (163816829, 271098230)`, found by extending the search over
`y` and the divisors `m` of `y² - 2` to `y ≤ 3·10⁸`. -/
theorem large_solutions_x_neg_448636753 (N : ℤ) :
    ∃ y z : ℤ, N ≤ y ∧ N ≤ z ∧
      y ^ 2 + (-448636753 : ℤ) ^ 2 * y + z ^ 2 * (-448636753) - 2 = 0 :=
  large_of_base 448636753 163816829 271098230 (by norm_num)
    (by simpa using not_isSquare_of_between 1794547012 42362 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) N
/-- **Quantitative form of Problem 2 for `y² + x²y + z²x - 2 = 0`.**
For every `k ≤ 448636753` the equation has an integer solution with
`min(|x|, |y|, |z|) ≥ k`.  (Sharper version of `problem2_le_10560367`.) -/
theorem problem2_le_448636753 {k : ℤ} (hk : k ≤ 448636753) :
    ∃ x y z : ℤ, y ^ 2 + x ^ 2 * y + z ^ 2 * x - 2 = 0 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| :=
  problem2_of_base 448636753 163816829 271098230 (by norm_num)
    (by simpa using not_isSquare_of_between 1794547012 42362 (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) hk
end Table5
