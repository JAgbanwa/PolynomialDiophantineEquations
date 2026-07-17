import Mathlib
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option autoImplicit false
/-- The Diophantine equation studied in the paper. -/
def IsSolution (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 - 2 = 0
/-- The ordered factor data canonically used when `x ≥ 2`. -/
def PositiveData (x y z d e s : ℤ) : Prop :=
  0 < d ∧ 0 < e ∧ 0 ≤ s ∧ d ≤ e ∧
  d * e = x ^ 3 - 2 ∧ d + e = s ^ 2 ∧
  (y = s ∨ y = -s) ∧ (z = -d ∨ z = -e)
/-- The ordered factor data canonically used when `x ≤ 1`. -/
def NegativeData (x y z d e s : ℤ) : Prop :=
  0 < d ∧ 0 < e ∧ 0 ≤ s ∧ d ≤ e ∧
  d * e = 2 - x ^ 3 ∧ e - d = s ^ 2 ∧
  (y = s ∨ y = -s) ∧ (z = d ∨ z = -e)
/-
No integral cube is equal to two (paper, Lemma 2.1).
-/
theorem cube_ne_two (x : ℤ) : x ^ 3 ≠ 2 := by
  exact fun h => by cases le_or_gt 2 x <;> nlinarith [ sq_nonneg ( x^2 ) ] ;
/-
The two factors occurring in the paper cannot vanish on a solution.
-/
theorem solution_factors_ne_zero {x y z : ℤ} (h : IsSolution x y z) :
    z ≠ 0 ∧ z + y ^ 2 ≠ 0 := by
  constructor
  · intro hz
    apply cube_ne_two x
    unfold IsSolution at h
    rw [hz] at h
    norm_num at h
    linarith
  · intro hfactor
    apply cube_ne_two x
    unfold IsSolution at h
    have hz : z = -y ^ 2 := by linarith
    rw [hz] at h
    ring_nf at h
    linarith
/-
The exact factor-pair correspondence (paper, Proposition 2.2).
-/
theorem factor_pair_iff (x y z : ℤ) :
    IsSolution x y z ↔
      (-z) * (z + y ^ 2) = x ^ 3 - 2 ∧ (-z) + (z + y ^ 2) = y ^ 2 := by
  grind +locals
/-
Conversely, any factor pair with the prescribed sum gives a solution.
-/
theorem solution_of_factor_pair {x y a b : ℤ}
    (hprod : a * b = x ^ 3 - 2) (hsum : a + b = y ^ 2) :
    IsSolution x y (-a) := by
  exact Eq.symm ( by linear_combination hprod + hsum * -a )
/-
The ordered factor pair attached to a solution is unique.
-/
theorem factor_pair_unique {y z a b : ℤ}
    (hsum : a + b = y ^ 2) (hz : z = -a) :
    a = -z ∧ b = z + y ^ 2 := by
  grobner
/-
Sign lemma used in the positive-product case (paper, Lemma 3.1).
-/
theorem positive_product_sign {a b : ℤ} (hp : 0 < a * b) (hs : 0 ≤ a + b) :
    0 < a ∧ 0 < b := by
  constructor <;> nlinarith
/-
Direct verification of construction I (paper, Lemma 3.3(a)).
-/
theorem positive_construction {x y d e s : ℤ}
    (hprod : d * e = x ^ 3 - 2) (hsum : d + e = s ^ 2)
    (hy : y = s ∨ y = -s) :
    IsSolution x y (-d) ∧ IsSolution x y (-e) := by
  rcases hy with rfl | rfl
  · constructor
    · exact solution_of_factor_pair hprod hsum
    · exact solution_of_factor_pair (x := x) (y := y) (a := e) (b := d)
        (by simpa [mul_comm] using hprod) (by simpa [add_comm] using hsum)
  · have hsum_neg : d + e = (-s) ^ 2 := by nlinarith
    constructor
    · exact solution_of_factor_pair hprod hsum_neg
    · exact solution_of_factor_pair (x := x) (y := -s) (a := e) (b := d)
        (by simpa [mul_comm] using hprod) (by simpa [add_comm] using hsum_neg)
/-
Direct verification of construction II (paper, Lemma 3.3(b)).
-/
theorem negative_construction {x y d e s : ℤ}
    (hprod : d * e = 2 - x ^ 3) (hdiff : e - d = s ^ 2)
    (hy : y = s ∨ y = -s) :
    IsSolution x y d ∧ IsSolution x y (-e) := by
  obtain rfl | rfl := hy;
  · constructor <;> unfold IsSolution <;> cases le_or_gt 0 d <;> cases le_or_gt 0 e <;> nlinarith;
  · constructor <;> unfold IsSolution <;> cases lt_or_ge 0 d <;> cases lt_or_ge 0 e <;> nlinarith
/-
Completeness of the canonical positive case.
-/
theorem positive_classification {x y z : ℤ} (hx : 2 ≤ x) :
    IsSolution x y z ↔ ∃ d e s : ℤ, PositiveData x y z d e s := by
  constructor
  · intro h
    have hpair := (factor_pair_iff x y z).mp h
    have hx3 : (2 : ℤ) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx 3
    have hprod_pos : 0 < (-z) * (z + y ^ 2) := by
      rw [hpair.1]
      norm_num at hx3 ⊢
      linarith
    have hsum_nonneg : 0 ≤ (-z) + (z + y ^ 2) := by
      rw [hpair.2]
      exact sq_nonneg y
    obtain ⟨ha, hb⟩ := positive_product_sign hprod_pos hsum_nonneg
    rcases le_total (-z) (z + y ^ 2) with hab | hba
    · refine ⟨-z, z + y ^ 2, |y|, ?_⟩
      unfold PositiveData
      refine ⟨ha, hb, abs_nonneg y, hab, hpair.1, ?_,
        eq_or_eq_neg_of_abs_eq rfl, Or.inl (by ring)⟩
      rw [sq_abs]
      exact hpair.2
    · refine ⟨z + y ^ 2, -z, |y|, ?_⟩
      unfold PositiveData
      refine ⟨hb, ha, abs_nonneg y, hba, ?_, ?_,
        eq_or_eq_neg_of_abs_eq rfl, Or.inr (by ring)⟩
      · rw [mul_comm]
        exact hpair.1
      · rw [add_comm, sq_abs]
        exact hpair.2
  · rintro ⟨d, e, s, hd, he, hs, hde, hprod, hsum, hy, hz⟩
    have hconstructed := positive_construction hprod hsum hy
    rcases hz with hz | hz
    · subst z
      exact hconstructed.1
    · subst z
      exact hconstructed.2
/-
Completeness of the canonical negative case.
-/
theorem negative_classification {x y z : ℤ} (hx : x ≤ 1) :
    IsSolution x y z ↔ ∃ d e s : ℤ, NegativeData x y z d e s := by
  constructor <;> intro h;
  · obtain ⟨a, b, hprod, hdiff⟩ : ∃ a b : ℤ, a * b = x ^ 3 - 2 ∧ a + b = y ^ 2 ∧ z = -a := by
      exact ⟨ -z, z + y ^ 2, by linarith [ h.symm ], by ring, by ring ⟩;
    by_cases ha : a < 0;
    · -- Since $a$ is negative, choose $d=-a$ and $e=b$.
      use -a, b, |y|;
      constructor <;> norm_num;
      · linarith;
      · exact ⟨ by nlinarith [ sq_nonneg x ], by nlinarith [ sq_nonneg x ], by linarith, by linarith, eq_or_eq_neg_of_abs_eq rfl, Or.inl hdiff.2 ⟩;
    · -- Since $a \geq 0$ and $a * b = x^3 - 2$, we have $b < 0$.
      have hb : b < 0 := by
        nlinarith [ show x ^ 3 < 2 by nlinarith [ sq_nonneg ( x^2 ) ] ];
      use -b, a, |y|;
      constructor <;> norm_num;
      · linarith;
      · exact ⟨ lt_of_le_of_ne ( le_of_not_gt ha ) ( Ne.symm <| by rintro rfl; nlinarith [ sq_nonneg x ] ), by nlinarith [ sq_nonneg x ], by linarith, hdiff.1, eq_or_eq_neg_of_abs_eq rfl, Or.inr hdiff.2 ⟩;
  · obtain ⟨d, e, s, _hd, _he, _hs, _hde, hprod, hdiff, hy, hz⟩ := h
    have hconstructed := negative_construction hprod hdiff hy
    rcases hz with rfl | rfl
    · exact hconstructed.1
    · exact hconstructed.2
/-
The complete two-case classification (paper, Theorem 4.1).
-/
theorem complete_classification (x y z : ℤ) :
    IsSolution x y z ↔
      (2 ≤ x ∧ ∃ d e s : ℤ, PositiveData x y z d e s) ∨
      (x ≤ 1 ∧ ∃ d e s : ℤ, NegativeData x y z d e s) := by
  constructor
  · intro hsol
    by_cases hx : 2 ≤ x
    · exact Or.inl ⟨hx, (positive_classification (x := x) (y := y) (z := z) hx).mp hsol⟩
    · have hx' : x ≤ 1 := by omega
      exact Or.inr ⟨hx', (negative_classification (x := x) (y := y) (z := z) hx').mp hsol⟩
  · rintro (⟨hx, hpos⟩ | ⟨hx, hneg⟩)
    · exact (positive_classification (x := x) (y := y) (z := z) hx).mpr hpos
    · exact (negative_classification (x := x) (y := y) (z := z) hx).mpr hneg
/-
Ordered positive factor data are unique.
-/
theorem positive_data_unique {x y z d e s d' e' s' : ℤ}
    (h : PositiveData x y z d e s) (h' : PositiveData x y z d' e' s') :
    d = d' ∧ e = e' ∧ s = s' := by
  -- From the definition of PositiveData,
  obtain ⟨hd_pos, he_pos, hs_nonneg, hd_le_e, hde, hs_sq, hy, hz⟩ := h
  obtain ⟨hd'_pos, he'_pos, hs'_nonneg, hd'_le_e', hde', hs'_sq, hy', hz'⟩ := h';
  grind
/-
Ordered negative factor data are unique.
-/
theorem negative_data_unique {x y z d e s d' e' s' : ℤ}
    (h : NegativeData x y z d e s) (h' : NegativeData x y z d' e' s') :
    d = d' ∧ e = e' ∧ s = s' := by
  obtain ⟨ hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hd₈ ⟩ := h
  obtain ⟨ hd₁', hd₂', hd₃', hd₄', hd₅', hd₆', hd₇', hd₈' ⟩ := h';
  grind
/-
Compact ordered-divisor formulation (paper, Corollary 5.1).
The quotient is avoided here by retaining the complementary factor explicitly.
-/
theorem ordered_divisor_parametrization (x y z : ℤ) :
    IsSolution x y z ↔
      ∃ a b s : ℤ, a ≠ 0 ∧ 0 ≤ s ∧ a * b = x ^ 3 - 2 ∧
        a + b = s ^ 2 ∧ (y = s ∨ y = -s) ∧ z = -a := by
  constructor <;> intro h;
  · exact ⟨ -z, z + y ^ 2, |y|, by
      exact neg_ne_zero.mpr ( solution_factors_ne_zero h |>.1 ), by
      positivity, by
      linarith [ h.symm ], by
      norm_num [ sq_abs ], by
      exact eq_or_eq_neg_of_abs_eq rfl, by
      ring ⟩;
  · obtain ⟨ a, b, s, ha, hs, hab, hs', hy, rfl ⟩ := h;
    cases hy <;> subst_vars <;> exact solution_of_factor_pair hab ( by linarith )
/-
For fixed `x`, there are only finitely many candidate ordered factors.
This is the termination fact behind the divisor algorithm of Proposition 6.1.
-/
theorem finite_ordered_factor_parameters (x : ℤ) :
    {a : ℤ | a ∣ x ^ 3 - 2}.Finite := by
  exact Set.Finite.subset ( Set.finite_Icc ( - |x ^ 3 - 2| ) |x ^ 3 - 2| ) fun a ha => ⟨ neg_le_of_abs_le <| Int.le_of_dvd ( abs_pos.mpr <| sub_ne_zero.mpr <| cube_ne_two x ) <| by simpa using ha, le_of_abs_le <| Int.le_of_dvd ( abs_pos.mpr <| sub_ne_zero.mpr <| cube_ne_two x ) <| by simpa using ha ⟩
/-
Swapping the two quadratic roots preserves the equation (paper, Proposition 5.2).
-/
theorem root_swap_solution {x y z : ℤ} (h : IsSolution x y z) :
    IsSolution x y (-y ^ 2 - z) := by
  unfold IsSolution at *; ring_nf at *; linarith;
/-
Root swapping is an involution.
-/
theorem root_swap_involution (y z : ℤ) :
    -y ^ 2 - (-y ^ 2 - z) = z := by
  grind
/-
The swap exchanges the ordered factors.
-/
theorem root_swap_factors (y z : ℤ) :
    (-(-y ^ 2 - z), (-y ^ 2 - z) + y ^ 2) = (z + y ^ 2, -z) := by
  grind
/-
A fixed point of root swapping can occur only in the positive case.
-/
theorem fixed_point_only_positive {x y z : ℤ} (hsol : IsSolution x y z)
    (hfix : -y ^ 2 - z = z) : 2 ≤ x := by
  -- Since $z \leq 0$, we have $x^3 - 2 = z^2 \geq 0$, which implies $x^3 \geq 2$.
  have hx3_ge_2 : x^3 ≥ 2 := by
    nlinarith [ hsol.symm ];
  nlinarith [ sq_nonneg ( x^2 ) ]
/-
In case I the square root parameter cannot vanish, as asserted in Theorem 4.1.
-/
theorem positive_data_parameter_pos {x y z d e s : ℤ}
    (h : PositiveData x y z d e s) : 0 < s := by
  obtain ⟨ hd, he, hs, hde, hsum, hy, hz ⟩ := h;
  nlinarith
/-
A diagonal pair in case II forces `s = 0` and hence `y = 0`.
-/
theorem negative_diagonal {x y z d e s : ℤ}
    (h : NegativeData x y z d e s) (hdiag : d = e) : s = 0 ∧ y = 0 := by
  obtain ⟨hd, he, hs, hde, hprod, hdiff, hy, hz⟩ := h
  have hs0 : s = 0 := by nlinarith [sq_nonneg s]
  constructor
  · exact hs0
  · rcases hy with hy | hy
    · linarith
    · linarith
/-
The two cases in the paper are exhaustive and mutually exclusive.
-/
theorem integer_case_split (x : ℤ) :
    (2 ≤ x ∨ x ≤ 1) ∧ ¬ (2 ≤ x ∧ x ≤ 1) := by
  omega
/-
The examples displayed in the paper all satisfy the equation.
-/
theorem paper_examples :
    IsSolution 1 0 1 ∧ IsSolution 1 0 (-1) ∧
    IsSolution 0 1 1 ∧ IsSolution 0 (-1) (-2) ∧
    IsSolution (-2) 3 1 ∧ IsSolution (-2) (-3) (-10) ∧
    IsSolution 8 7 (-15) ∧ IsSolution 8 (-7) (-34) ∧
    IsSolution 20 17 (-31) ∧ IsSolution 20 (-17) (-258) := by
  unfold IsSolution; norm_num;
/-
The two admissible pairs at `x = 26` give the eight solutions stated in the paper.
-/
theorem paper_example_twenty_six :
    ∀ y ∈ ([19, -19, 17, -17] : List ℤ),
      (y.natAbs = 19 → IsSolution 26 y (-58) ∧ IsSolution 26 y (-303)) ∧
      (y.natAbs = 17 → IsSolution 26 y (-87) ∧ IsSolution 26 y (-202)) := by
  norm_num [IsSolution]
