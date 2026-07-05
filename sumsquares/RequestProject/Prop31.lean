import RequestProject.Represent
/-!
# Proposition 3.1: the shortest previously-open equation
We prove that the equation `y² + x³y + z² + 1 = 0` (equation (2) of the paper) has
infinitely many integer solutions, via the fact that `x⁶ − 4` is a sum of two squares
for infinitely many integers `x`.
The application of Algorithm 2.2 uses `f = −4`, `u = 162`, for which
`4(u³+f) = 17006096` and the auxiliary equation is
`17006096 x² − 688752720 = v²`, with seed solution
`x₀ = 22108343594783571`, `v₀ = 91171377945572295096`.
-/
namespace SumSquares
open scoped BigOperators
/-- Infinitely many integers `x` have `x⁶ − 4` a sum of two squares. -/
lemma sqSum_x6_sub_four_infinite :
    {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + (-4))}.Infinite := by
  refine cube_sqSum_infinite (f := -4) (u := 162) ?_ ?_ ?_
    (x0 := 22108343594783571) (v0 := 91171377945572295096) ?_ ?_ ?_
  · norm_num
  · exact ⟨700, 4064, by norm_num⟩
  · native_decide
  · norm_num
  · norm_num
  · norm_num
/-
From `x⁶ − 4 ∈ S₂` one obtains an integer solution of equation (2).
-/
lemma sol_of_x6_sub_four {x : ℤ} (h : SqSum (x ^ 6 + (-4))) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0 := by
  obtain ⟨A, B, hA, hB⟩ : ∃ A B : ℤ, x^6 + (-4) = A^2 + B^2 ∧ A % 2 = x % 2 ∧ B % 2 = 0 :=
    sqSum_even_split rfl h
  obtain ⟨ z, rfl ⟩ := Int.modEq_zero_iff_dvd.mp hB.2;
  -- Since $A \equiv x \pmod{2}$, we have $A = x^3 + 2y$ for some integer $y$.
  obtain ⟨ y, hy ⟩ : ∃ y : ℤ, A = x^3 + 2 * y := by
    exact ⟨ ( A - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( Int.dvd_of_emod_eq_zero ( by norm_num [ Int.sub_emod, Int.mul_emod, pow_three, hB ] ; have := Int.emod_nonneg x two_ne_zero; have := Int.emod_lt_of_pos x two_pos; interval_cases x % 2 <;> trivial ) ) ] ; ring ⟩;
  exact ⟨ y, z, by subst hy; linarith ⟩
/-- **Proposition 3.1.** The equation `y² + x³y + z² + 1 = 0` has infinitely many
integer solutions. -/
theorem prop_3_1 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_of_first_proj
    (P := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0)
    (S := {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + (-4))})
    sqSum_x6_sub_four_infinite
  intro x hx
  exact sol_of_x6_sub_four hx.2
end SumSquares
