import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Conditional finiteness of the solutions of `x ^ 3 * y ^ 2 = z ^ 4 + 1`

This file formalises the argument of the accompanying note
`abc_finiteness_x3y2_z4_plus1.pdf`: assuming the `abc` conjecture, the Diophantine
equation `x ^ 3 * y ^ 2 = z ^ 4 + 1` has only finitely many solutions in integers.

The proof runs as follows.  Write `N = z ^ 4 + 1 = x ^ 3 * y ^ 2` and `t = |z|`.
Every prime dividing `N` divides `x * y`, so `rad N ^ 2 ∣ N`, i.e. `N` is powerful and
`rad N ≤ N ^ (1 / 2)`.  Moreover `rad (t ^ 4) = rad t ≤ t ≤ N ^ (1 / 4)`.
Since `1 + t ^ 4 = N` is a coprime triple, the `abc` conjecture with `ε = 1 / 6` gives
`N ≤ K * rad (t ^ 4 * N) ^ (7 / 6) ≤ K * N ^ (7 / 8)`, whence `N ≤ K ^ 8`.
All of `x`, `|y|`, `|z|` are then bounded in terms of `K` alone, so there are only
finitely many solutions.

(Rational exponents are avoided in the formal proof by working with the equivalent
integral inequalities `rad (t ^ 4 * N) ^ 4 ≤ N ^ 3` and `N ^ 3 ≤ K ^ 24`.)
-/

namespace AbcFiniteness

/-- The radical of a natural number: the product of its distinct prime divisors
(with `rad 0 = rad 1 = 1`). -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The `abc` conjecture: for every `ε > 0` there is a constant `K ≥ 1` such that all
pairwise coprime positive integers `a, b, c` with `a + b = c` satisfy
`c ≤ K * rad (a * b * c) ^ (1 + ε)`. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 1 ≤ K ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c → a + b = c →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-! ### Elementary properties of the radical -/

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_le_self {n : ℕ} (hn : 0 < n) : rad n ≤ n := Nat.le_of_dvd hn (rad_dvd n)

lemma rad_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) : rad (n ^ k) = rad n := by
  unfold rad
  rw [Nat.primeFactors_pow n hk]

lemma rad_mul_le {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : rad (m * n) ≤ rad m * rad n := by
  unfold rad
  rw [Nat.primeFactors_mul hm hn]
  calc ∏ p ∈ m.primeFactors ∪ n.primeFactors, p
      ≤ (∏ p ∈ m.primeFactors ∪ n.primeFactors, p) *
          ∏ p ∈ m.primeFactors ∩ n.primeFactors, p :=
        Nat.le_mul_of_pos_right _ (Finset.prod_pos fun _ hp =>
          (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_inter_left hp)).pos)
    _ = _ := Finset.prod_union_inter

/-! ### The key arithmetic facts -/

/-- A number of the shape `X ^ 3 * Y ^ 2` (with `X, Y > 0`) is powerful:
the square of its radical divides it. -/
lemma rad_sq_dvd {X Y : ℕ} (hX : 0 < X) (hY : 0 < Y) :
    rad (X ^ 3 * Y ^ 2) ^ 2 ∣ X ^ 3 * Y ^ 2 := by
  have hXY : rad (X ^ 3 * Y ^ 2) = rad (X * Y) := by
    unfold rad
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_mul hX.ne' hY.ne',
      Nat.primeFactors_pow X (by norm_num), Nat.primeFactors_pow Y (by norm_num)]
  rw [hXY]
  refine (pow_dvd_pow_of_dvd (rad_dvd _) 2).trans ?_
  rw [show (X * Y) ^ 2 = X ^ 2 * Y ^ 2 by ring]
  exact mul_dvd_mul (pow_dvd_pow X (by norm_num)) dvd_rfl

/-- Consequently `rad N ^ 2 ≤ N` for `N = X ^ 3 * Y ^ 2`. -/
lemma rad_sq_le {X Y : ℕ} (hX : 0 < X) (hY : 0 < Y) :
    rad (X ^ 3 * Y ^ 2) ^ 2 ≤ X ^ 3 * Y ^ 2 :=
  Nat.le_of_dvd (by positivity) (rad_sq_dvd hX hY)

/-- The radical bound `rad (T ^ 4 * N) ^ 4 ≤ N ^ 3` for `N = T ^ 4 + 1 = X ^ 3 * Y ^ 2`,
which is the integral form of `rad (t ^ 4 * N) ≤ N ^ (3 / 4)`. -/
lemma rad_bound {X Y T : ℕ} (hX : 0 < X) (hY : 0 < Y) (hT : 0 < T)
    (h : X ^ 3 * Y ^ 2 = T ^ 4 + 1) :
    rad (T ^ 4 * (T ^ 4 + 1)) ^ 4 ≤ (T ^ 4 + 1) ^ 3 := by
  set N := T ^ 4 + 1 with hN
  have hNpos : 0 < N := by positivity
  -- `rad (T ^ 4 * N) ≤ T * rad N`
  have h1 : rad (T ^ 4 * N) ≤ T * rad N := by
    refine (rad_mul_le (by positivity) hNpos.ne').trans ?_
    exact Nat.mul_le_mul_right _ ((rad_pow T (by norm_num)).le.trans (rad_le_self hT))
  -- `rad N ^ 2 ≤ N`
  have h2 : rad N ^ 2 ≤ N := by rw [← h]; exact rad_sq_le hX hY
  have h3 : T ^ 4 ≤ N := by omega
  calc rad (T ^ 4 * N) ^ 4 ≤ (T * rad N) ^ 4 := Nat.pow_le_pow_left h1 4
    _ = T ^ 4 * (rad N ^ 2) ^ 2 := by ring
    _ ≤ N * N ^ 2 := Nat.mul_le_mul h3 (Nat.pow_le_pow_left h2 2)
    _ = N ^ 3 := by ring

/-- The real-analytic core of the `abc` step: if `N ≤ K * R ^ (7 / 6)` and
`R ^ 4 ≤ N ^ 3`, then `N ^ 3 ≤ K ^ 24`. -/
lemma pow_bound_of_abc {N R K : ℝ} (hN : 0 < N) (hR : 0 ≤ R) (hK : 1 ≤ K)
    (h : N ≤ K * R ^ (1 + (1 : ℝ) / 6)) (h2 : R ^ (4 : ℕ) ≤ N ^ (3 : ℕ)) :
    N ^ (3 : ℕ) ≤ K ^ (24 : ℕ) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have key : N ^ (24 : ℕ) ≤ K ^ (24 : ℕ) * R ^ (28 : ℕ) := by
    have h24 : N ^ (24 : ℕ) ≤ (K * R ^ (1 + (1 : ℝ) / 6)) ^ (24 : ℕ) :=
      pow_le_pow_left₀ hN.le h 24
    refine h24.trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast (R ^ (1 + (1 : ℝ) / 6)) 24, ← Real.rpow_mul hR,
      ← Real.rpow_natCast R 28]
    norm_num
  have h28 : R ^ (28 : ℕ) ≤ (N ^ (3 : ℕ)) ^ (7 : ℕ) := by
    calc R ^ (28 : ℕ) = (R ^ (4 : ℕ)) ^ (7 : ℕ) := by ring
      _ ≤ (N ^ (3 : ℕ)) ^ (7 : ℕ) := pow_le_pow_left₀ (by positivity) h2 7
  have hfin : N ^ (3 : ℕ) * N ^ (21 : ℕ) ≤ K ^ (24 : ℕ) * N ^ (21 : ℕ) := by
    calc N ^ (3 : ℕ) * N ^ (21 : ℕ) = N ^ (24 : ℕ) := by ring
      _ ≤ K ^ (24 : ℕ) * R ^ (28 : ℕ) := key
      _ ≤ K ^ (24 : ℕ) * (N ^ (3 : ℕ)) ^ (7 : ℕ) := mul_le_mul_of_nonneg_left h28 (by positivity)
      _ = K ^ (24 : ℕ) * N ^ (21 : ℕ) := by ring
  exact le_of_mul_le_mul_right hfin (by positivity)

/-- **Key bound.**  Under the `abc` conjecture there is a constant `K ≥ 1` (namely the
constant `K` attached to `ε = 1/6`) such that every solution in positive naturals of
`X ^ 3 * Y ^ 2 = T ^ 4 + 1` satisfies `X ^ 3 * Y ^ 2 ≤ K ^ 8`. -/
theorem exists_const_bound (habc : ABCConjecture) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X Y T : ℕ, 0 < X → 0 < Y → X ^ 3 * Y ^ 2 = T ^ 4 + 1 →
      ((X ^ 3 * Y ^ 2 : ℕ) : ℝ) ≤ K ^ (8 : ℕ) := by
  obtain ⟨K, hK, hKabc⟩ := habc (1 / 6) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro X Y T hX hY h
  rw [h]
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show ((0 ^ 4 + 1 : ℕ) : ℝ) = 1 by norm_num]
    exact one_le_pow₀ hK
  set N := T ^ 4 + 1 with hNdef
  have hNpos : 0 < N := by positivity
  have hT4 : 0 < T ^ 4 := by positivity
  -- apply the `abc` conjecture to `1 + T ^ 4 = N`
  have habc' := hKabc 1 (T ^ 4) N Nat.one_pos hT4 hNpos (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (by simp [hNdef, Nat.Coprime]) (by omega)
  rw [one_mul] at habc'
  -- the radical bound, in real form
  have hrad : ((rad (T ^ 4 * N) : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) := by
    have := rad_bound hX hY hT h
    exact_mod_cast this
  have hcube : ((N : ℝ)) ^ (3 : ℕ) ≤ K ^ (24 : ℕ) :=
    pow_bound_of_abc (by exact_mod_cast hNpos) (by positivity) hK habc' hrad
  -- `N ^ 3 ≤ (K ^ 8) ^ 3` gives `N ≤ K ^ 8`
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  calc ((N : ℝ)) ^ (3 : ℕ) ≤ K ^ (24 : ℕ) := hcube
    _ = (K ^ (8 : ℕ)) ^ (3 : ℕ) := by ring

/-- **Main bound.**  Under the `abc` conjecture there is a natural number bound `B` such
that every solution in positive naturals of `X ^ 3 * Y ^ 2 = T ^ 4 + 1` satisfies
`X ^ 3 * Y ^ 2 ≤ B`. -/
theorem exists_bound (habc : ABCConjecture) :
    ∃ B : ℕ, ∀ X Y T : ℕ, 0 < X → 0 < Y → X ^ 3 * Y ^ 2 = T ^ 4 + 1 →
      X ^ 3 * Y ^ 2 ≤ B := by
  obtain ⟨K, hK, hKbound⟩ := exists_const_bound habc
  refine ⟨⌈K ^ (8 : ℕ)⌉₊, fun X Y T hX hY h => ?_⟩
  have := (hKbound X Y T hX hY h).trans (Nat.le_ceil (K ^ (8 : ℕ)))
  exact_mod_cast this

/-- Rewriting an integer solution of `x ^ 3 * y ^ 2 = z ^ 4 + 1` as a solution in
positive natural numbers. -/
lemma nat_form {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 + 1) :
    0 < x ∧ y ≠ 0 ∧ x.toNat ^ 3 * y.natAbs ^ 2 = z.natAbs ^ 4 + 1 := by
  have hz : (0 : ℤ) ≤ z ^ 4 := by positivity
  have hy : y ≠ 0 := by rintro rfl; simp at h; nlinarith
  have hy2 : 0 < y ^ 2 := by positivity
  have hx : 0 < x := by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have h3 : x ^ 3 < 0 := Odd.pow_neg (by decide) hx
      nlinarith
    · subst hx; simp at h; nlinarith
    · exact hx
  refine ⟨hx, hy, ?_⟩
  rw [← Int.natCast_inj (m := x.toNat ^ 3 * y.natAbs ^ 2) (n := z.natAbs ^ 4 + 1)]
  push_cast [Int.toNat_of_nonneg hx.le]
  rw [sq_abs, show |z| ^ 4 = z ^ 4 by rw [← abs_pow, abs_of_nonneg hz]]
  exact h

/-- The equation does have solutions: `(1, 1, 0)` and `(1, -1, 0)`.  In particular the
finiteness statement below is not vacuous. -/
lemma mem_solutions_one : ((1 : ℤ), (1 : ℤ), (0 : ℤ)) ∈
      {p : ℤ × ℤ × ℤ | p.1 ^ 3 * p.2.1 ^ 2 = p.2.2 ^ 4 + 1} ∧
    ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) ∈ {p : ℤ × ℤ × ℤ | p.1 ^ 3 * p.2.1 ^ 2 = p.2.2 ^ 4 + 1} := by
  constructor <;> simp [Set.mem_ofPred_eq]

/-- **Theorem 1 (explicit bounds).**  Assuming the `abc` conjecture, there is a constant
`K ≥ 1` such that every integer solution of `x ^ 3 * y ^ 2 = z ^ 4 + 1` satisfies
`1 ≤ x`, `y ≠ 0`, and `x ^ 3 ≤ K ^ 8`, `y ^ 2 ≤ K ^ 8`, `z ^ 4 ≤ K ^ 8`.
These are exactly the bounds `1 ≤ x ≤ K ^ (8 / 3)`, `1 ≤ |y| ≤ K ^ 4`, `|z| ≤ K ^ 2`
of the note, written without fractional exponents. -/
theorem solution_bounds (habc : ABCConjecture) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x y z : ℤ, x ^ 3 * y ^ 2 = z ^ 4 + 1 →
      1 ≤ x ∧ y ≠ 0 ∧ (x : ℝ) ^ 3 ≤ K ^ (8 : ℕ) ∧ (y : ℝ) ^ 2 ≤ K ^ (8 : ℕ) ∧
        (z : ℝ) ^ 4 ≤ K ^ (8 : ℕ) := by
  obtain ⟨K, hK, hKbound⟩ := exists_const_bound habc
  refine ⟨K, hK, fun x y z hp => ?_⟩
  obtain ⟨hx, hy, heq⟩ := nat_form hp
  set X := x.toNat with hX
  set Y := y.natAbs with hY
  set T := z.natAbs with hT
  have hXpos : 0 < X := by omega
  have hYpos : 0 < Y := Int.natAbs_pos.mpr hy
  have hM : ((X ^ 3 * Y ^ 2 : ℕ) : ℝ) ≤ K ^ (8 : ℕ) := hKbound X Y T hXpos hYpos heq
  -- the three natural-number inequalities
  have h1 : X ^ 3 ≤ X ^ 3 * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : Y ^ 2 ≤ X ^ 3 * Y ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
  have h3 : T ^ 4 ≤ X ^ 3 * Y ^ 2 := by omega
  -- transfer to the integers
  have hxc : (x : ℝ) = (X : ℝ) := by
    have : (X : ℤ) = x := Int.toNat_of_nonneg hx.le
    exact_mod_cast this.symm
  have hyc : (y : ℝ) ^ 2 = (Y : ℝ) ^ 2 := by
    have : ((Y : ℤ)) ^ 2 = y ^ 2 := by rw [hY, Int.natAbs_sq]
    exact_mod_cast this.symm
  have hzc : (z : ℝ) ^ 4 = (T : ℝ) ^ 4 := by
    have : ((T : ℤ)) ^ 4 = z ^ 4 := by
      rw [hT, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Int.natAbs_sq, ← pow_mul]
    exact_mod_cast this.symm
  refine ⟨hx, hy, ?_, ?_, ?_⟩
  · rw [hxc]
    refine le_trans ?_ hM
    exact_mod_cast h1
  · rw [hyc]
    refine le_trans ?_ hM
    exact_mod_cast h2
  · rw [hzc]
    refine le_trans ?_ hM
    exact_mod_cast h3

/-- **Finiteness.**  Assuming the `abc` conjecture, the equation `x ^ 3 * y ^ 2 = z ^ 4 + 1`
has only finitely many solutions in integers. -/
theorem finite_solutions (habc : ABCConjecture) :
    {p : ℤ × ℤ × ℤ | p.1 ^ 3 * p.2.1 ^ 2 = p.2.2 ^ 4 + 1}.Finite := by
  obtain ⟨B, hB⟩ := exists_bound habc
  refine Set.Finite.subset (Set.finite_Icc ((-(B : ℤ), -(B : ℤ), -(B : ℤ)))
    (((B : ℤ), (B : ℤ), (B : ℤ)))) ?_
  rintro ⟨x, y, z⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  obtain ⟨hx, hy, heq⟩ := nat_form hp
  set X := x.toNat with hX
  set Y := y.natAbs with hY
  set T := z.natAbs with hT
  have hXpos : 0 < X := by omega
  have hYpos : 0 < Y := Int.natAbs_pos.mpr hy
  have hle : X ^ 3 * Y ^ 2 ≤ B := hB X Y T hXpos hYpos heq
  have hXB : X ≤ B := le_trans (le_trans (Nat.le_self_pow (by norm_num) X)
    (Nat.le_mul_of_pos_right _ (by positivity))) hle
  have hYB : Y ≤ B := le_trans (le_trans (Nat.le_self_pow (by norm_num) Y)
    (Nat.le_mul_of_pos_left _ (by positivity))) hle
  have hTB : T ≤ B := by
    have h1 : T ^ 4 + 1 ≤ B := heq ▸ hle
    have h2 : T ≤ T ^ 4 := Nat.le_self_pow (by norm_num) T
    omega
  have hxB : x ≤ (B : ℤ) := by omega
  have hyB : |y| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hYB
  have hzB : |z| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hTB
  have hy1 := abs_le.mp hyB
  have hz1 := abs_le.mp hzB
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩ <;>
    simp only [Prod.mk_le_mk] <;>
    refine ⟨by omega, by omega, by omega⟩

end AbcFiniteness
