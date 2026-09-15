/-
# Table 1, equation `x^2 y + y^2 z + z^2 x = 1`

One of the eighteen Diophantine equations of length `9` listed in Table 1 of
*On the polynomial values represented by quadratic forms* (B. Grechuk, J. Agbanwa),
for which it is unknown whether the integer solution set is finite or infinite.

Unconditional results proved in this file:

* the cyclic symmetry of the solution set;
* in every solution the three coordinates are pairwise coprime;
* the complete description of the solutions with `x = 0` (and, by symmetry, with `y = 0`
  or `z = 0`);
* a "second root" (Vieta) description of the quadratic in `z`;
* several large solutions, exhibiting that solutions are not confined to small numbers;
* the complete list of solutions in the box `[-20, 20]^3`.
-/
import Mathlib

namespace Table1Eq04

set_option maxRecDepth 1000000

/-- The equation of Table 1: `x ^ 2 * y + y ^ 2 * z + z ^ 2 * x = 1`. -/
def IsSol (x y z : ℤ) : Prop := x ^ 2 * y + y ^ 2 * z + z ^ 2 * x = 1

instance (x y z : ℤ) : Decidable (IsSol x y z) := by
  unfold IsSol; infer_instance

/-! ### Examples of solutions -/

theorem isSol_one_one_zero : IsSol 1 1 0 := by decide

theorem isSol_neg_three : IsSol (-3) 4 7 := by decide

theorem isSol_nine : IsSol 9 (-19) (-44) := by decide

theorem isSol_neg_ten : IsSol (-10) (-53) 279 := by decide

theorem isSol_large : IsSol (-1091) 1308 2213 := by
  unfold IsSol; norm_num

theorem isSol_large' : IsSol 141 980 (-6791) := by
  unfold IsSol; norm_num

/-! ### Symmetries -/

/-- The solution set is invariant under the cyclic shift `(x, y, z) ↦ (y, z, x)`. -/
theorem isSol_cyclic {x y z : ℤ} (h : IsSol x y z) : IsSol y z x := by
  unfold IsSol at h ⊢; linear_combination h

/-- Vieta jumping in the variable `z`: the equation is a quadratic in `z` whose two roots
sum to `-y ^ 2 / x`.  If `w` is the second root then `(x, y, w)` is again a solution. -/
theorem isSol_other_root {x y z w : ℤ} (h : IsSol x y z) (hw : x * (z + w) = -y ^ 2) :
    IsSol x y w := by
  unfold IsSol at h ⊢
  linear_combination h + (w - z) * hw

/-! ### Coprimality -/

/-- In any solution `x` and `y` are coprime. -/
theorem gcd_xy {x y z : ℤ} (h : IsSol x y z) : Int.gcd x y = 1 := by
  unfold IsSol at h
  have key : ∀ d : ℤ, d ∣ x → d ∣ y → d ∣ 1 := by
    rintro d ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨d ^ 2 * a ^ 2 * b + d * b ^ 2 * z + z ^ 2 * a, by rw [← h, ha, hb]; ring⟩
  have hd := key ((Int.gcd x y : ℕ) : ℤ) (Int.gcd_dvd_left x y) (Int.gcd_dvd_right x y)
  have : Int.gcd x y ∣ 1 := by exact_mod_cast hd
  exact Nat.dvd_one.1 this

/-- In any solution `y` and `z` are coprime. -/
theorem gcd_yz {x y z : ℤ} (h : IsSol x y z) : Int.gcd y z = 1 :=
  gcd_xy (isSol_cyclic h)

/-- In any solution `z` and `x` are coprime. -/
theorem gcd_zx {x y z : ℤ} (h : IsSol x y z) : Int.gcd z x = 1 :=
  gcd_xy (isSol_cyclic (isSol_cyclic h))

/-! ### Solutions with a vanishing coordinate -/

/-- The solutions with `x = 0` are exactly `(0, 1, 1)` and `(0, -1, 1)`. -/
theorem sols_x_zero {y z : ℤ} (h : IsSol 0 y z) : z = 1 ∧ (y = 1 ∨ y = -1) := by
  unfold IsSol at h
  have hy : y ^ 2 * z = 1 := by linarith
  have hz : z ∣ 1 := ⟨y ^ 2, by linear_combination -hy⟩
  have hz1 : z = 1 ∨ z = -1 := Int.isUnit_iff.1 (isUnit_of_dvd_one hz)
  rcases hz1 with hz1 | hz1 <;> subst hz1
  · refine ⟨rfl, ?_⟩
    have hy2 : (y - 1) * (y + 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.1 hy2 with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · exfalso
    nlinarith [sq_nonneg y]

/-! ### Exhaustive search in a box -/

set_option maxHeartbeats 4000000 in
/-- All solutions in the box `[-20, 20]^3`. -/
theorem box_20 : ∀ x ∈ Finset.Icc (-20 : ℤ) 20, ∀ y ∈ Finset.Icc (-20 : ℤ) 20,
    ∀ z ∈ Finset.Icc (-20 : ℤ) 20, IsSol x y z →
      (x, y, z) = (-3, 4, 7) ∨ (x, y, z) = (-2, 1, -1) ∨ (x, y, z) = (-2, 3, -1) ∨
      (x, y, z) = (-1, -2, 1) ∨ (x, y, z) = (-1, -2, 3) ∨ (x, y, z) = (-1, 1, 0) ∨
      (x, y, z) = (-1, 1, 1) ∨ (x, y, z) = (0, -1, 1) ∨ (x, y, z) = (0, 1, 1) ∨
      (x, y, z) = (1, -1, -2) ∨ (x, y, z) = (1, -1, 1) ∨ (x, y, z) = (1, 0, -1) ∨
      (x, y, z) = (1, 0, 1) ∨ (x, y, z) = (1, 1, -1) ∨ (x, y, z) = (1, 1, 0) ∨
      (x, y, z) = (3, -1, -2) ∨ (x, y, z) = (4, 7, -3) ∨ (x, y, z) = (7, -3, 4) := by
  decide

end Table1Eq04
