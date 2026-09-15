/-
# Table 1, equation `z^2 + y^2 z + x^3 - x - 1 = 0`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* explicit solutions and two symmetries of the solution set;
* the factorised form `(-z) * (z + y ^ 2) = x ^ 3 - x - 1`;
* solvability criteria for fixed `x`, resp. fixed `x` and `y`;
* there is no solution with `z = 0`;
* in every solution `y` is divisible by `6` and `z` is odd;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq02

set_option maxRecDepth 1000000

/-- The equation of Table 1: `z ^ 2 + y ^ 2 * z + x ^ 3 - x - 1 = 0`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 - x - 1 = 0

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

private lemma emod_of_cast {n : ℕ} {a r : ℤ} (h : (a : ZMod n) = (r : ZMod n)) :
    a % (n : ℤ) = r % (n : ℤ) :=
  (ZMod.intCast_eq_intCast_iff a r n).1 h

/-! ### Examples of solutions -/

theorem isSol_zero : IsSol 0 0 1 := by decide

theorem isSol_one : IsSol 1 0 1 := by decide

theorem isSol_neg_three : IsSol (-3) 0 5 := by decide

theorem isSol_neg_five : IsSol (-5) 0 11 := by decide

/-! ### Symmetries -/

theorem isSol_neg_y {x y z : ℤ} (h : IsSol x y z) : IsSol x (-y) z := by
  unfold IsSol at h ⊢; linear_combination h

/-- For fixed `x` and `y` the two roots of the quadratic in `z` are `z` and `-y ^ 2 - z`. -/
theorem isSol_other_root {x y z : ℤ} (h : IsSol x y z) : IsSol x y (-y ^ 2 - z) := by
  unfold IsSol at h ⊢; linear_combination h

/-! ### Factorised form and criteria -/

theorem isSol_iff_factor (x y z : ℤ) : IsSol x y z ↔ (-z) * (z + y ^ 2) = x ^ 3 - x - 1 := by
  unfold IsSol
  constructor <;> intro h <;> linear_combination -h

/-- For a fixed `x`, the equation is solvable iff `x ^ 3 - x - 1` can be written as a
product `a * b` of two integers whose sum is a perfect square. -/
theorem exists_sol_iff_factorisation (x : ℤ) :
    (∃ y z, IsSol x y z) ↔ ∃ a b y : ℤ, a * b = x ^ 3 - x - 1 ∧ a + b = y ^ 2 := by
  constructor
  · rintro ⟨y, z, h⟩
    exact ⟨-z, z + y ^ 2, y, (isSol_iff_factor x y z).1 h, by ring⟩
  · rintro ⟨a, b, y, hab, hsum⟩
    refine ⟨y, -a, ?_⟩
    rw [isSol_iff_factor]
    have hb : b = y ^ 2 - a := by linarith
    rw [← hab, hb]; ring

/-- For fixed `x` and `y`, solvability is equivalent to the discriminant being a square. -/
theorem exists_sol_iff_disc (x y : ℤ) :
    (∃ z, IsSol x y z) ↔ ∃ w : ℤ, w ^ 2 = y ^ 4 - 4 * (x ^ 3 - x - 1) := by
  constructor
  · rintro ⟨z, h⟩
    refine ⟨2 * z + y ^ 2, ?_⟩
    unfold IsSol at h
    linear_combination 4 * h
  · rintro ⟨w, hw⟩
    have h2 : ((w : ZMod 2)) ^ 2 = ((y : ZMod 2)) ^ 4 := by
      have hc := congrArg (fun n : ℤ => (n : ZMod 2)) hw
      push_cast at hc
      have h40 : (4 : ZMod 2) = 0 := by decide
      rw [h40] at hc
      simpa using hc
    have hcast : (((w - y ^ 2 : ℤ)) : ZMod 2) = 0 := by
      push_cast
      revert h2
      generalize ((w : ZMod 2)) = a
      generalize ((y : ZMod 2)) = b
      revert a b
      decide
    obtain ⟨t, ht⟩ : (2 : ℤ) ∣ w - y ^ 2 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (w - y ^ 2) 2).1 hcast
      exact_mod_cast this
    refine ⟨t, ?_⟩
    unfold IsSol
    have hwt : w = y ^ 2 + 2 * t := by linarith
    subst hwt
    nlinarith [hw]

/-! ### No solution with `z = 0` -/

theorem no_sol_z_zero (x y : ℤ) : ¬ IsSol x y 0 := by
  intro h
  unfold IsSol at h
  have hx : x ^ 3 - x - 1 = 0 := by linarith
  rcases le_or_gt x 1 with h1 | h1
  · nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (x - 1)]
  · nlinarith [sq_nonneg x]

/-! ### Congruence obstructions -/

/-- In every solution `y` is divisible by `6`. -/
theorem six_dvd_y {x y z : ℤ} (h : IsSol x y z) : y % 6 = 0 := by
  have h3 : ((z : ZMod 3)) ^ 2 + (y : ZMod 3) ^ 2 * (z : ZMod 3)
      + (x : ZMod 3) ^ 3 - (x : ZMod 3) - 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 3)) h
    push_cast at this
    exact this
  have h4 : ((z : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 * (z : ZMod 4)
      + (x : ZMod 4) ^ 3 - (x : ZMod 4) - 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 4)) h
    push_cast at this
    exact this
  have hy3 : ((y : ZMod 3)) = ((0 : ℤ) : ZMod 3) := by
    push_cast
    revert h3
    generalize ((x : ZMod 3)) = a
    generalize ((y : ZMod 3)) = b
    generalize ((z : ZMod 3)) = c
    revert a b c
    decide
  have hy4 : ((y : ZMod 4)) = ((0 : ℤ) : ZMod 4) ∨ ((y : ZMod 4)) = ((2 : ℤ) : ZMod 4) := by
    push_cast
    revert h4
    generalize ((x : ZMod 4)) = a
    generalize ((y : ZMod 4)) = b
    generalize ((z : ZMod 4)) = c
    revert a b c
    decide
  have e3 := emod_of_cast hy3
  rcases hy4 with hy4 | hy4
  · have := emod_of_cast hy4; omega
  · have := emod_of_cast hy4; omega

/-- In every solution `z` is odd. -/
theorem z_odd {x y z : ℤ} (h : IsSol x y z) : z % 2 ≠ 0 := by
  intro hz
  have h2 : ((z : ZMod 2)) ^ 2 + (y : ZMod 2) ^ 2 * (z : ZMod 2)
      + (x : ZMod 2) ^ 3 - (x : ZMod 2) - 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 2)) h
    push_cast at this
    exact this
  have hz2 : ((z : ZMod 2)) = ((0 : ℤ) : ZMod 2) :=
    (ZMod.intCast_eq_intCast_iff z 0 2).2 (by show z % (2 : ℤ) = 0 % (2 : ℤ); omega)
  rw [hz2] at h2
  revert h2
  push_cast
  generalize ((x : ZMod 2)) = a
  generalize ((y : ZMod 2)) = b
  revert a b
  decide

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`; note that all of them have `y = 0`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      y = 0 ∧ ((x, z) = (-5, -11) ∨ (x, z) = (-5, 11) ∨ (x, z) = (-3, -5) ∨ (x, z) = (-3, 5) ∨
        (x, z) = (-1, -1) ∨ (x, z) = (-1, 1) ∨ (x, z) = (0, -1) ∨ (x, z) = (0, 1) ∨
        (x, z) = (1, -1) ∨ (x, z) = (1, 1)) := by
  decide

end Table1Eq02
