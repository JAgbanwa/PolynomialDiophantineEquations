/-
# Table 1, equation `z^2 + y^2 z + x^3 - 2 = 0`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* explicit solutions, and two symmetries of the solution set;
* the factorised form `(-z) * (z + y ^ 2) = x ^ 3 - 2`;
* a criterion: for a fixed `x` a solution exists iff `x ^ 3 - 2` admits a factorisation
  `a * b` with `a + b` a perfect square; and for fixed `x, y` iff a discriminant is a square;
* there is no solution with `z = 0`;
* congruence obstructions `x % 4 ≠ 3`, `x % 5 ≠ 4`, `z % 4 ≠ 0`;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq01

set_option maxRecDepth 1000000

/-- The equation of Table 1: `z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

/-! ### Examples of solutions -/

theorem isSol_one_zero_one : IsSol 1 0 1 := by decide

theorem isSol_zero_one_one : IsSol 0 1 1 := by decide

theorem isSol_neg_seven : IsSol (-7) 8 5 := by decide

theorem isSol_eight : IsSol 8 7 (-15) := by decide

/-! ### Symmetries -/

theorem isSol_neg_y {x y z : ℤ} (h : IsSol x y z) : IsSol x (-y) z := by
  unfold IsSol at h ⊢; linear_combination h

/-- For fixed `x` and `y` the two roots of the quadratic in `z` are `z` and `-y ^ 2 - z`. -/
theorem isSol_other_root {x y z : ℤ} (h : IsSol x y z) : IsSol x y (-y ^ 2 - z) := by
  unfold IsSol at h ⊢; linear_combination h

/-! ### Factorised form and criteria -/

theorem isSol_iff_factor (x y z : ℤ) : IsSol x y z ↔ (-z) * (z + y ^ 2) = x ^ 3 - 2 := by
  unfold IsSol
  constructor <;> intro h <;> linear_combination -h

/-- For a fixed `x`, the equation is solvable iff `x ^ 3 - 2` can be written as a product
`a * b` of two integers whose sum is a perfect square. -/
theorem exists_sol_iff_factorisation (x : ℤ) :
    (∃ y z, IsSol x y z) ↔ ∃ a b y : ℤ, a * b = x ^ 3 - 2 ∧ a + b = y ^ 2 := by
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
    (∃ z, IsSol x y z) ↔ ∃ w : ℤ, w ^ 2 = y ^ 4 - 4 * (x ^ 3 - 2) := by
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
  have hx : x ^ 3 = 2 := by linarith
  rcases le_or_gt x 1 with h1 | h1
  · nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
  · nlinarith [sq_nonneg x]

/-! ### Congruence obstructions -/

theorem x_mod_four {x y z : ℤ} (h : IsSol x y z) : x % 4 ≠ 3 := by
  intro hx
  have h4 : ((z : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 * (z : ZMod 4) + (x : ZMod 4) ^ 3 - 2 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 4)) h
    push_cast at this
    exact this
  have hx4 : ((x : ZMod 4)) = ((3 : ℤ) : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff x 3 4).2 (by show x % (4 : ℤ) = 3 % (4 : ℤ); omega)
  rw [hx4] at h4
  revert h4
  push_cast
  generalize ((y : ZMod 4)) = b
  generalize ((z : ZMod 4)) = c
  revert b c
  decide

theorem x_mod_five {x y z : ℤ} (h : IsSol x y z) : x % 5 ≠ 4 := by
  intro hx
  have h5 : ((z : ZMod 5)) ^ 2 + (y : ZMod 5) ^ 2 * (z : ZMod 5) + (x : ZMod 5) ^ 3 - 2 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 5)) h
    push_cast at this
    exact this
  have hx5 : ((x : ZMod 5)) = ((4 : ℤ) : ZMod 5) :=
    (ZMod.intCast_eq_intCast_iff x 4 5).2 (by show x % (5 : ℤ) = 4 % (5 : ℤ); omega)
  rw [hx5] at h5
  revert h5
  push_cast
  generalize ((y : ZMod 5)) = b
  generalize ((z : ZMod 5)) = c
  revert b c
  decide

theorem z_mod_four {x y z : ℤ} (h : IsSol x y z) : z % 4 ≠ 0 := by
  intro hz
  have h4 : ((z : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 * (z : ZMod 4) + (x : ZMod 4) ^ 3 - 2 = 0 := by
    have := congrArg (fun n : ℤ => (n : ZMod 4)) h
    push_cast at this
    exact this
  have hz4 : ((z : ZMod 4)) = ((0 : ℤ) : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff z 0 4).2 (by show z % (4 : ℤ) = 0 % (4 : ℤ); omega)
  rw [hz4] at h4
  revert h4
  push_cast
  generalize ((x : ZMod 4)) = a
  generalize ((y : ZMod 4)) = b
  revert a b
  decide

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      (x, y, z) = (-7, -8, 5) ∨ (x, y, z) = (-7, 8, 5) ∨
      (x, y, z) = (-2, -3, -10) ∨ (x, y, z) = (-2, -3, 1) ∨
      (x, y, z) = (-2, 3, -10) ∨ (x, y, z) = (-2, 3, 1) ∨
      (x, y, z) = (0, -1, -2) ∨ (x, y, z) = (0, -1, 1) ∨
      (x, y, z) = (0, 1, -2) ∨ (x, y, z) = (0, 1, 1) ∨
      (x, y, z) = (1, 0, -1) ∨ (x, y, z) = (1, 0, 1) ∨
      (x, y, z) = (8, -7, -15) ∨ (x, y, z) = (8, 7, -15) := by
  decide

end Table1Eq01
