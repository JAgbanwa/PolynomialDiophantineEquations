import RequestProject.Represent
/-!
# Proposition 3.2: four further length-9 equations
We prove that each of the equations (14)–(17) of the paper has infinitely many
integer solutions:
* (14) `y² + x³y + z² − 2 = 0`      (from `x⁶ + 8 ∈ S₂` infinitely often),
* (15) `y² + x³y + z² + z − 1 = 0`  (from `x⁶ + 5 ∈ S₂` infinitely often),
* (16) `y² + x³y + z² + z + 1 = 0`  (from `x⁶ − 3 ∈ S₂` infinitely often),
* (17) `y² + x³y + y + z² + 1 = 0`  (from `(x³+1)² − 4 ∈ S₂` infinitely often,
  obtained via `x = −w²` and the factorization `(w⁶−3)(w⁶+1)`).
-/
namespace SumSquares
open scoped BigOperators
/-! ## Infinitude of the relevant sum-of-two-squares values -/
lemma sqSum_x6_add_eight_infinite :
    {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + 8)}.Infinite := by
  refine cube_sqSum_infinite (f := 8) (u := 8) ?_ ?_ ?_
    (x0 := 12) (v0 := 544) ?_ ?_ ?_
  · norm_num
  · exact ⟨44, 12, by norm_num⟩
  · native_decide
  · norm_num
  · norm_num
  · norm_num
lemma sqSum_x6_add_five_infinite :
    {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + 5)}.Infinite := by
  refine cube_sqSum_infinite (f := 5) (u := 2) ?_ ?_ ?_
    (x0 := 6) (v0 := 44) ?_ ?_ ?_
  · norm_num
  · exact ⟨6, 4, by norm_num⟩
  · native_decide
  · norm_num
  · norm_num
  · norm_num
lemma sqSum_x6_sub_three_infinite :
    {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + (-3))}.Infinite := by
  refine cube_sqSum_infinite (f := -3) (u := 2) ?_ ?_ ?_
    (x0 := 2) (v0 := 4) ?_ ?_ ?_
  · norm_num
  · exact ⟨4, 2, by norm_num⟩
  · native_decide
  · norm_num
  · norm_num
  · norm_num
lemma sqSum_x6_sub_three_even_infinite :
    {x : ℤ | 0 < x ∧ Even x ∧ SqSum (x ^ 6 + (-3))}.Infinite := by
  refine cube_sqSum_even_infinite (f := -3) (u := 2) ?_ ?_ ?_
    (w0 := 1) (v0 := 4) ?_ ?_ ?_
  · norm_num
  · exact ⟨4, 2, by norm_num⟩
  · native_decide
  · norm_num
  · norm_num
  · norm_num
/-! ## Solution production -/
lemma sol_14 {x : ℤ} (h : SqSum (x ^ 6 + 8)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0 := by
  -- By `sqSum_even_split (f := 8) (by decide) h`, obtain A B with x^6+8 = A^2+B^2, A%2 = x%2, B%2 = 0.
  obtain ⟨A, B, hAB⟩ : ∃ A B : ℤ, x ^ 6 + 8 = A ^ 2 + B ^ 2 ∧ A % 2 = x % 2 ∧ B % 2 = 0 := by
    exact sqSum_even_split ( by decide ) h;
  obtain ⟨y, hy⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y := by
    exact ⟨ ( A - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( Int.dvd_of_emod_eq_zero <| by norm_num [ Int.sub_emod, Int.mul_emod, pow_three, hAB ] ; have := Int.emod_nonneg x two_ne_zero; have := Int.emod_lt_of_pos x two_pos; interval_cases x % 2 <;> simp_all +decide ) ] ; ring ⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, B = 2 * z := by
    exact Int.modEq_zero_iff_dvd.mp hAB.2.2
  use y, z;
  subst_vars; linarith;
lemma sol_15 {x : ℤ} (h : SqSum (x ^ 6 + 5)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0 := by
  obtain ⟨ A, B, h₁, h₂, h₃ ⟩ := sqSum_odd_split ( by decide ) h;
  -- Since $A$ and $x$ have the same parity, $x^3$ and $A$ have the same parity.
  have h_parity : (x ^ 3 - A) % 2 = 0 := by
    norm_num [ Int.sub_emod, pow_succ, Int.mul_emod, h₂ ];
    cases Int.emod_two_eq_zero_or_one x <;> simp +decide [ * ];
  -- From B%2 = 1 obtain z with B = 2*z + 1.
  obtain ⟨ z, hz ⟩ : ∃ z : ℤ, B = 2 * z + 1 := by
    exact Int.odd_iff.2 h₃;
  obtain ⟨ y, hy ⟩ := Int.modEq_zero_iff_dvd.mp h_parity;
  exact ⟨ -y, z, by rw [ show A = x ^ 3 - 2 * y by linarith ] at h₁; rw [ hz ] at h₁; linarith ⟩
lemma sol_16 {x : ℤ} (h : SqSum (x ^ 6 + (-3))) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0 := by
  obtain ⟨ A, B, h ⟩ := SumSquares.sqSum_odd_split ( by decide ) h;
  -- Since $B$ is odd, we can write $B = 2z + 1$ for some integer $z$.
  obtain ⟨ z, hz ⟩ : ∃ z : ℤ, B = 2 * z + 1 := by
    exact Int.odd_iff.2 h.2.2;
  obtain ⟨ y, hy ⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y ∨ A = -x ^ 3 - 2 * y := by
    have h_even : (A - x ^ 3) % 2 = 0 := by
      norm_num [ Int.sub_emod, Int.mul_emod, pow_three, h ];
      cases Int.emod_two_eq_zero_or_one x <;> simp +decide [ * ];
    exact ⟨ ( A - x ^ 3 ) / 2, Or.inl ( by linarith [ Int.emod_add_mul_ediv ( A - x ^ 3 ) 2 ] ) ⟩;
  rcases hy with ( rfl | rfl ) <;> [ exact ⟨ y, z, by subst hz; linarith ⟩ ; exact ⟨ -y - x ^ 3, z, by subst hz; linarith ⟩ ]
/-
General odd split: an odd sum of two squares is `(odd)² + (even)²`.
-/
lemma sqSum_split_of_odd {N : ℤ} (hodd : N % 2 = 1) (h : SqSum N) :
    ∃ A B : ℤ, N = A ^ 2 + B ^ 2 ∧ A % 2 = 1 ∧ B % 2 = 0 := by
  rcases h with ⟨ A, B, rfl ⟩;
  cases Int.emod_two_eq_zero_or_one A <;> cases Int.emod_two_eq_zero_or_one B <;> simp_all +decide [ sq, Int.add_emod, Int.mul_emod ];
  · exact ⟨ B, A, by ring, by assumption, by assumption ⟩;
  · exact ⟨ A, B, rfl, by assumption, by assumption ⟩
lemma sol_17_of {w : ℤ} (hw : Even w) (h : SqSum (w ^ 6 + (-3))) :
    ∃ y z : ℤ, y ^ 2 + (-w ^ 2) ^ 3 * y + y + z ^ 2 + 1 = 0 := by
  -- Set x := -w^2, so x^3 = (-w^2)^3 = -w^6.
  set x : ℤ := -w^2;
  obtain ⟨A, B, hN, hA, hB⟩ : ∃ A B : ℤ, ((x ^ 3 + 1) ^ 2 - 4) = A ^ 2 + B ^ 2 ∧ A % 2 = 1 ∧ B % 2 = 0 := by
    convert sqSum_split_of_odd _ _;
    · obtain ⟨ k, rfl ⟩ := hw; ring_nf; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] ;
      grind +locals;
    · convert sqSum_mul h ( show SqSum ( w ^ 6 + 1 ) from ⟨ w ^ 3, 1, by ring ⟩ ) using 1 ; ring;
  obtain ⟨y, hy⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y + 1 := by
    use (A - x ^ 3 - 1) / 2;
    linarith [ Int.ediv_mul_cancel ( show 2 ∣ A - x ^ 3 - 1 from Int.dvd_of_emod_eq_zero ( by norm_num [ Int.sub_emod, Int.add_emod, pow_succ, Int.mul_emod, hA, show x % 2 = 0 from Int.emod_eq_zero_of_dvd <| dvd_neg.mpr <| dvd_pow ( even_iff_two_dvd.mp hw ) two_ne_zero ] ) ) ]
  obtain ⟨z, hz⟩ : ∃ z : ℤ, B = 2 * z := by
    exact Int.modEq_zero_iff_dvd.mp hB;
  exact ⟨ y, z, by subst_vars; linarith ⟩
/-! ## The propositions -/
/-- Equation (14) has infinitely many integer solutions. -/
theorem prop_3_2_14 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite := by
  apply infinite_of_first_proj
    (P := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0)
    (S := {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + 8)})
    sqSum_x6_add_eight_infinite
  intro x hx
  exact sol_14 hx.2
/-- Equation (15) has infinitely many integer solutions. -/
theorem prop_3_2_15 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite := by
  apply infinite_of_first_proj
    (P := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0)
    (S := {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + 5)})
    sqSum_x6_add_five_infinite
  intro x hx
  exact sol_15 hx.2
/-- Equation (16) has infinitely many integer solutions. -/
theorem prop_3_2_16 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite := by
  apply infinite_of_first_proj
    (P := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0)
    (S := {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + (-3))})
    sqSum_x6_sub_three_infinite
  intro x hx
  exact sol_16 hx.2
/-- Equation (17) has infinitely many integer solutions. -/
theorem prop_3_2_17 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_of_first_proj_comp
    (P := fun x y z => y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1 = 0)
    (S := {x : ℤ | 0 < x ∧ Even x ∧ SqSum (x ^ 6 + (-3))})
    sqSum_x6_sub_three_even_infinite (φ := fun w => -w ^ 2)
  · intro a ha b hb hab
    have hab' : -a ^ 2 = -b ^ 2 := hab
    have hsq : a ^ 2 = b ^ 2 := by linarith
    have hfac : (a - b) * (a + b) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have := ha.1; have := hb.1; linarith
  · intro w hw
    exact sol_17_of hw.2.1 hw.2.2
end SumSquares
