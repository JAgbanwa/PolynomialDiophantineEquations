/-
# Table 1, equation `y (x^3 - z^2) = 2x - 1`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* explicit solutions and the symmetry `z ↦ -z`;
* in every solution `y ≠ 0`, `x ^ 3 - z ^ 2 ≠ 0`, and both `y` and `x ^ 3 - z ^ 2`
  divide `2x - 1`; thus the equation asks for the Hall difference `x ^ 3 - z ^ 2`
  to be a divisor of `2x - 1`;
* the complete list of solutions with `z = 0`, and with `x = 0`;
* in every solution `y` is odd and `y % 3 ≠ 2`;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq07

set_option maxRecDepth 1000000

private lemma emod_of_cast {n : ℕ} {a r : ℤ} (h : (a : ZMod n) = (r : ZMod n)) :
    a % (n : ℤ) = r % (n : ℤ) :=
  (ZMod.intCast_eq_intCast_iff a r n).1 h

/-- The equation of Table 1: `y * (x ^ 3 - z ^ 2) = 2 * x - 1`. -/
def IsSol (x y z : ℤ) : Prop := y * (x ^ 3 - z ^ 2) = 2 * x - 1

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

/-! ### Examples of solutions -/

theorem isSol_one : IsSol 1 1 0 := by decide

theorem isSol_zero : IsSol 0 1 1 := by decide

theorem isSol_two : IsSol 2 (-3) 3 := by decide

theorem isSol_neg_one : IsSol (-1) 3 0 := by decide

/-! ### Symmetry -/

theorem isSol_neg_z {x y z : ℤ} (h : IsSol x y z) : IsSol x y (-z) := by
  unfold IsSol at h ⊢; linear_combination h

/-! ### Basic divisibility structure -/

theorem y_ne_zero {x y z : ℤ} (h : IsSol x y z) : y ≠ 0 := by
  rintro rfl
  unfold IsSol at h
  omega

theorem cube_sub_sq_ne_zero {x y z : ℤ} (h : IsSol x y z) : x ^ 3 - z ^ 2 ≠ 0 := by
  intro h0
  unfold IsSol at h
  rw [h0] at h
  omega

theorem y_dvd {x y z : ℤ} (h : IsSol x y z) : y ∣ 2 * x - 1 :=
  ⟨x ^ 3 - z ^ 2, h.symm⟩

theorem cube_sub_sq_dvd {x y z : ℤ} (h : IsSol x y z) : (x ^ 3 - z ^ 2) ∣ 2 * x - 1 := by
  unfold IsSol at h
  exact ⟨y, by linear_combination -h⟩

/-! ### Solutions with a vanishing coordinate -/

/-- The only solutions with `z = 0` are `(1, 1, 0)` and `(-1, 3, 0)`. -/
theorem sols_z_zero {x y : ℤ} (h : IsSol x y 0) : (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = 3) := by
  unfold IsSol at h
  have hx : x ∣ 1 := by
    have h1 : x ∣ 2 * x - 1 := ⟨x ^ 2 * y, by linear_combination -h⟩
    have h2 : x ∣ 2 * x := ⟨2, by ring⟩
    have h3 := dvd_sub h2 h1
    have h4 : 2 * x - (2 * x - 1) = 1 := by ring
    rwa [h4] at h3
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hx) with hx1 | hx1 <;> subst hx1
  · left; exact ⟨rfl, by linarith⟩
  · right; exact ⟨rfl, by linarith⟩

/-- The only solutions with `x = 0` are `(0, 1, 1)` and `(0, 1, -1)`. -/
theorem sols_x_zero {y z : ℤ} (h : IsSol 0 y z) : y = 1 ∧ (z = 1 ∨ z = -1) := by
  unfold IsSol at h
  have hzy : y * (z ^ 2) = 1 := by linear_combination -h
  have hz : z ^ 2 ∣ 1 := ⟨y, by linear_combination h⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hz) with hz1 | hz1
  · rw [hz1] at hzy
    have hzz : (z - 1) * (z + 1) = 0 := by linear_combination hz1
    refine ⟨by linarith, ?_⟩
    rcases mul_eq_zero.1 hzz with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · exfalso; nlinarith [sq_nonneg z]

/-! ### Congruence obstructions -/

/-- In every solution `y` is odd. -/
theorem y_odd {x y z : ℤ} (h : IsSol x y z) : y % 2 ≠ 0 := by
  intro hy
  have h2 : ((y : ZMod 2)) * ((x : ZMod 2) ^ 3 - (z : ZMod 2) ^ 2) = 2 * (x : ZMod 2) - 1 := by
    have := congrArg (fun n : ℤ => (n : ZMod 2)) h
    push_cast at this
    exact this
  have hy2 : ((y : ZMod 2)) = ((0 : ℤ) : ZMod 2) :=
    (ZMod.intCast_eq_intCast_iff y 0 2).2 (by show y % (2 : ℤ) = 0 % (2 : ℤ); omega)
  rw [hy2] at h2
  revert h2
  push_cast
  generalize ((x : ZMod 2)) = a
  generalize ((z : ZMod 2)) = c
  revert a c
  decide

/-- In every solution `y % 3 ≠ 2`. -/
theorem y_mod_three {x y z : ℤ} (h : IsSol x y z) : y % 3 ≠ 2 := by
  intro hy
  have h3 : ((y : ZMod 3)) * ((x : ZMod 3) ^ 3 - (z : ZMod 3) ^ 2) = 2 * (x : ZMod 3) - 1 := by
    have := congrArg (fun n : ℤ => (n : ZMod 3)) h
    push_cast at this
    exact this
  have hy3 : ((y : ZMod 3)) = ((2 : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff y 2 3).2 (by show y % (3 : ℤ) = 2 % (3 : ℤ); omega)
  rw [hy3] at h3
  revert h3
  push_cast
  generalize ((x : ZMod 3)) = a
  generalize ((z : ZMod 3)) = c
  revert a c
  decide

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      (x, y, z) = (-1, 3, 0) ∨ (x, y, z) = (0, 1, -1) ∨ (x, y, z) = (0, 1, 1) ∨
      (x, y, z) = (1, 1, 0) ∨ (x, y, z) = (2, -3, -3) ∨ (x, y, z) = (2, -3, 3) := by
  decide

end Table1Eq07
