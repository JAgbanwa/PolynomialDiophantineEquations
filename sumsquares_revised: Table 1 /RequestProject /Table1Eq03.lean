/-
# Table 1, equation `z^2 + y^2 z + x^3 y + 1 = 0`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* explicit solutions and the symmetries `(x, y, z) ↦ (-x, -y, z)`, `z ↦ -y ^ 2 - z`;
* the factorised form `(-z) * (z + y ^ 2) = x ^ 3 y + 1`;
* a solvability criterion for fixed `x, y` (square discriminant);
* the two solutions with `z = 0` are `(1, -1, 0)` and `(-1, 1, 0)`;
* in every solution `x` is odd, `y` is not divisible by `3`, and `y` is not divisible by `4`;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq03

set_option maxRecDepth 1000000

/-- The equation of Table 1: `z ^ 2 + y ^ 2 * z + x ^ 3 * y + 1 = 0`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 * y + 1 = 0

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

private lemma emod_of_cast {n : ℕ} {a r : ℤ} (h : (a : ZMod n) = (r : ZMod n)) :
    a % (n : ℤ) = r % (n : ℤ) :=
  (ZMod.intCast_eq_intCast_iff a r n).1 h

/-! ### Examples of solutions -/

theorem isSol_one : IsSol 1 (-1) 0 := by decide

theorem isSol_neg_one : IsSol (-1) 1 0 := by decide

theorem isSol_neg_seven : IsSol (-7) 1 18 := by decide

theorem isSol_three : IsSol 3 5 (-8) := by decide

/-! ### Symmetries -/

theorem isSol_neg {x y z : ℤ} (h : IsSol x y z) : IsSol (-x) (-y) z := by
  unfold IsSol at h ⊢; linear_combination h

/-- For fixed `x` and `y` the two roots of the quadratic in `z` are `z` and `-y ^ 2 - z`. -/
theorem isSol_other_root {x y z : ℤ} (h : IsSol x y z) : IsSol x y (-y ^ 2 - z) := by
  unfold IsSol at h ⊢; linear_combination h

/-! ### Factorised form and criterion -/

theorem isSol_iff_factor (x y z : ℤ) : IsSol x y z ↔ (-z) * (z + y ^ 2) = x ^ 3 * y + 1 := by
  unfold IsSol
  constructor <;> intro h <;> linear_combination -h

/-- For fixed `x` and `y`, solvability is equivalent to the discriminant being a square. -/
theorem exists_sol_iff_disc (x y : ℤ) :
    (∃ z, IsSol x y z) ↔ ∃ w : ℤ, w ^ 2 = y ^ 4 - 4 * (x ^ 3 * y + 1) := by
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

/-! ### The solutions with `z = 0` -/

theorem sols_z_zero {x y : ℤ} (h : IsSol x y 0) : (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) := by
  unfold IsSol at h
  have hxy : x ^ 3 * y = -1 := by linarith
  have hx : x ∣ 1 := by
    refine ⟨-(x ^ 2 * y), ?_⟩
    linear_combination hxy
  have hx1 : x = 1 ∨ x = -1 := Int.isUnit_iff.1 (isUnit_of_dvd_one hx)
  rcases hx1 with hx1 | hx1 <;> subst hx1
  · left; constructor; · rfl
    linarith [hxy]
  · right; constructor; · rfl
    nlinarith [hxy]

/-! ### Congruence obstructions -/

/-- In every solution `x` is odd. -/
theorem x_odd {x y z : ℤ} (h : IsSol x y z) : x % 2 ≠ 0 := by
  intro hx
  have h4 : ((z : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 * (z : ZMod 4)
      + (x : ZMod 4) ^ 3 * (y : ZMod 4) + 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 4)) h
    push_cast at this
    exact this
  have hcases : x % 4 = 0 ∨ x % 4 = 2 := by omega
  rcases hcases with hc | hc
  · have hx4 : ((x : ZMod 4)) = ((0 : ℤ) : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff x 0 4).2 (by show x % (4 : ℤ) = 0 % (4 : ℤ); omega)
    rw [hx4] at h4
    revert h4
    push_cast
    generalize ((y : ZMod 4)) = b
    generalize ((z : ZMod 4)) = c
    revert b c
    decide
  · have hx4 : ((x : ZMod 4)) = ((2 : ℤ) : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff x 2 4).2 (by show x % (4 : ℤ) = 2 % (4 : ℤ); omega)
    rw [hx4] at h4
    revert h4
    push_cast
    generalize ((y : ZMod 4)) = b
    generalize ((z : ZMod 4)) = c
    revert b c
    decide

/-- In every solution `y` is not divisible by `3`. -/
theorem y_not_dvd_three {x y z : ℤ} (h : IsSol x y z) : y % 3 ≠ 0 := by
  intro hy
  have h3 : ((z : ZMod 3)) ^ 2 + (y : ZMod 3) ^ 2 * (z : ZMod 3)
      + (x : ZMod 3) ^ 3 * (y : ZMod 3) + 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 3)) h
    push_cast at this
    exact this
  have hy3 : ((y : ZMod 3)) = ((0 : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff y 0 3).2 (by show y % (3 : ℤ) = 0 % (3 : ℤ); omega)
  rw [hy3] at h3
  revert h3
  push_cast
  generalize ((x : ZMod 3)) = a
  generalize ((z : ZMod 3)) = c
  revert a c
  decide

/-- In every solution `y` is not divisible by `4`. -/
theorem y_not_dvd_four {x y z : ℤ} (h : IsSol x y z) : y % 4 ≠ 0 := by
  intro hy
  have h4 : ((z : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 * (z : ZMod 4)
      + (x : ZMod 4) ^ 3 * (y : ZMod 4) + 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 4)) h
    push_cast at this
    exact this
  have hy4 : ((y : ZMod 4)) = ((0 : ℤ) : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff y 0 4).2 (by show y % (4 : ℤ) = 0 % (4 : ℤ); omega)
  rw [hy4] at h4
  revert h4
  push_cast
  generalize ((x : ZMod 4)) = a
  generalize ((z : ZMod 4)) = c
  revert a c
  decide

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      (x, y, z) = (-7, 1, -19) ∨ (x, y, z) = (-7, 1, 18) ∨
      (x, y, z) = (-3, -5, -17) ∨ (x, y, z) = (-3, -5, -8) ∨
      (x, y, z) = (-1, -2, -3) ∨ (x, y, z) = (-1, -2, -1) ∨
      (x, y, z) = (-1, 1, -1) ∨ (x, y, z) = (-1, 1, 0) ∨
      (x, y, z) = (1, -1, -1) ∨ (x, y, z) = (1, -1, 0) ∨
      (x, y, z) = (1, 2, -3) ∨ (x, y, z) = (1, 2, -1) ∨
      (x, y, z) = (3, 5, -17) ∨ (x, y, z) = (3, 5, -8) ∨
      (x, y, z) = (7, -1, -19) ∨ (x, y, z) = (7, -1, 18) := by
  decide

end Table1Eq03
