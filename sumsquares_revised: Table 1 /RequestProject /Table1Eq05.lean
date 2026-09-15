/-
# Table 1, equation `x^4 + y^3 + z^2 + 1 = 0`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* explicit solutions and the symmetries `x ↦ -x`, `z ↦ -z`;
* the equivalent Hall-type form `(-y) ^ 3 - z ^ 2 = x ^ 4 + 1`;
* in every solution `y ≤ -1`;
* in every solution `y % 8 ∈ {3, 5, 7}`; in particular `y` is odd;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq05

set_option maxRecDepth 1000000

/-- The equation of Table 1: `x ^ 4 + y ^ 3 + z ^ 2 + 1 = 0`. -/
def IsSol (x y z : ℤ) : Prop := x ^ 4 + y ^ 3 + z ^ 2 + 1 = 0

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

private lemma emod_of_cast {n : ℕ} {a r : ℤ} (h : (a : ZMod n) = (r : ZMod n)) :
    a % (n : ℤ) = r % (n : ℤ) :=
  (ZMod.intCast_eq_intCast_iff a r n).1 h

/-! ### Examples of solutions -/

theorem isSol_zero : IsSol 0 (-1) 0 := by decide

theorem isSol_one : IsSol 1 (-3) 5 := by decide

theorem isSol_neg_one : IsSol (-1) (-3) (-5) := by decide

/-! ### Symmetries -/

theorem isSol_neg_x {x y z : ℤ} (h : IsSol x y z) : IsSol (-x) y z := by
  unfold IsSol at h ⊢; linear_combination h

theorem isSol_neg_z {x y z : ℤ} (h : IsSol x y z) : IsSol x y (-z) := by
  unfold IsSol at h ⊢; linear_combination h

/-! ### Equivalent Hall-type form -/

/-- The equation says exactly that `x ^ 4 + 1` is a difference of the cube `(-y) ^ 3`
and the square `z ^ 2`. -/
theorem isSol_iff (x y z : ℤ) : IsSol x y z ↔ (-y) ^ 3 - z ^ 2 = x ^ 4 + 1 := by
  unfold IsSol
  constructor <;> intro h <;> linear_combination -h

/-! ### Sign of `y` -/

theorem y_le_neg_one {x y z : ℤ} (h : IsSol x y z) : y ≤ -1 := by
  unfold IsSol at h
  by_contra hy
  push_neg at hy
  have hy0 : 0 ≤ y := by omega
  nlinarith [pow_nonneg hy0 3, sq_nonneg z, sq_nonneg (x ^ 2)]

/-! ### Congruence obstruction modulo 8 -/

/-- In every solution `y % 8 ∈ {3, 5, 7}`; in particular `y` is odd. -/
theorem y_mod_eight {x y z : ℤ} (h : IsSol x y z) : y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by
  have h8 : ((x : ZMod 8)) ^ 4 + (y : ZMod 8) ^ 3 + (z : ZMod 8) ^ 2 + 1 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at this
    exact this
  have hy : ((y : ZMod 8)) = ((3 : ℤ) : ZMod 8) ∨ ((y : ZMod 8)) = ((5 : ℤ) : ZMod 8) ∨
      ((y : ZMod 8)) = ((7 : ℤ) : ZMod 8) := by
    push_cast
    revert h8
    generalize ((x : ZMod 8)) = a
    generalize ((y : ZMod 8)) = b
    generalize ((z : ZMod 8)) = c
    revert a b c
    decide
  rcases hy with hy | hy | hy
  · have := emod_of_cast hy; omega
  · have := emod_of_cast hy; omega
  · have := emod_of_cast hy; omega

theorem y_odd {x y z : ℤ} (h : IsSol x y z) : y % 2 ≠ 0 := by
  have := y_mod_eight h
  omega

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      (x, y, z) = (-1, -3, -5) ∨ (x, y, z) = (-1, -3, 5) ∨ (x, y, z) = (0, -1, 0) ∨
      (x, y, z) = (1, -3, -5) ∨ (x, y, z) = (1, -3, 5) := by
  decide

end Table1Eq05
