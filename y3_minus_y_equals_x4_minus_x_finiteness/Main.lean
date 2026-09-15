import Mathlib

/-!
# `y³ - y = x⁴ - x` : a formalization of the finiteness paper

This file formalizes the mathematical content of the note
*"A correction to the proposed infinitude `y³ - y = x⁴ - x`: an unconditional finiteness
argument with its theorem dependence explicit"*.

The note argues:

1. (Elementary check) If `|x|` is a perfect cube then the only solutions are
   `x ∈ {0, 1}`, `y ∈ {-1, 0, 1}`.
2. The affine curve `F(x,y) = y³ - y - x⁴ + x = 0` is irreducible over `ℂ`.
3. Its projective closure `H(X,Y,Z) = Y³Z - YZ³ - X⁴ + XZ³ = 0` is a *smooth* plane quartic
   (no affine singularities, and the unique point at infinity `[0 : 1 : 0]` is smooth).
4. A smooth plane quartic has genus `3 ≥ 1`, so Siegel's theorem on integral points gives
   finiteness of the integer solutions.

Everything in items 1–3 is proved here in full.  Item 4 uses Siegel's theorem, which the note
itself states as an external, unproved input; Siegel's theorem is not available in Mathlib.
Accordingly it is *not* introduced as an axiom: it appears as an explicit hypothesis
`SiegelForSmoothPlaneQuartics` of the final theorem
`y3_sub_y_eq_x4_sub_x_finite_of_siegel`.  The hypothesis is stated for *arbitrary* smooth
plane quartics over `ℚ` (a smooth plane quartic automatically has genus `3`, so this is a
genuine special case of Siegel's theorem and not a restatement of the desired conclusion).

Conclusion about the paper's claim: the paper is correct.  The set of integer solutions is
indeed finite, the geometric computations in the paper are correct, and the proof is
unconditional but not self-contained (it rests on Siegel's theorem).  As the paper says,
completeness of the list of six displayed solutions is not proved; we do verify here by an
exhaustive check that they are the only solutions with `|x| ≤ 4`.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace CubicQuarticFiniteness

/-! ## 0. The six solutions listed in the paper -/

/-- The six solutions displayed in the paper really are solutions. -/
theorem six_solutions :
    ∀ p ∈ ({(0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)} : Finset (ℤ × ℤ)),
      p.2 ^ 3 - p.2 = p.1 ^ 4 - p.1 := by
  decide

/-! ## 1. Proposition 1 of the paper: the case where `|x|` is a perfect cube -/

private lemma cube_sub_self_nonneg {z : ℤ} (hz : 1 ≤ z) : 0 ≤ z ^ 3 - z := by
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ z) (by nlinarith : (0:ℤ) ≤ z ^ 2 - 1)]

private lemma cube_sub_self_nonpos {y : ℤ} (hy : y ≤ 1) : y ^ 3 - y ≤ 0 := by
  rcases le_or_gt y (-1) with h | h
  · have := cube_sub_self_nonneg (z := -y) (by linarith)
    nlinarith
  · interval_cases y <;> norm_num

/-- `f(s) = s³ - s` is monotone on the positive integers. -/
private lemma cube_sub_self_mono {a b : ℤ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a ^ 3 - a ≤ b ^ 3 - b := by
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ b - a)
    (by nlinarith : (0:ℤ) ≤ a ^ 2 + a * b + b ^ 2 - 1)]

private lemma cube_sub_self_eq_zero {y : ℤ} (h : y ^ 3 - y = 0) : y = -1 ∨ y = 0 ∨ y = 1 := by
  have h' : y * (y - 1) * (y + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

/-- The main step of Proposition 1: if `x = ±t³` with `t ≥ 2`, then `x⁴ - x` lies strictly
between the two consecutive values `f(t⁴)` and `f(t⁴+1)` of `f(s) = s³ - s`, so it is not of
the form `y³ - y`. -/
private lemma no_solution_of_two_le (x y t : ℤ) (ht : 2 ≤ t) (hx : x = t ^ 3 ∨ x = -t ^ 3)
    (h : y ^ 3 - y = x ^ 4 - x) : False := by
  have h3 : (8:ℤ) ≤ t ^ 3 := by
    calc (8:ℤ) = 2 ^ 3 := by norm_num
      _ ≤ t ^ 3 := by gcongr
  have h9 : (8:ℤ) ≤ t ^ 9 := by
    calc (8:ℤ) ≤ 2 ^ 9 := by norm_num
      _ ≤ t ^ 9 := by gcongr
  have h34 : t ^ 3 < t ^ 4 := by nlinarith
  have h12 : t ^ 12 = (t ^ 4) ^ 3 := by ring
  have h8 : 0 < t ^ 8 := by positivity
  have hx4 : x ^ 4 = t ^ 12 := by rcases hx with rfl | rfl <;> ring
  have hxlt : x ≤ t ^ 3 := by rcases hx with rfl | rfl <;> linarith
  have hxgt : -t ^ 3 ≤ x := by rcases hx with rfl | rfl <;> linarith
  have hN : y ^ 3 - y = t ^ 12 - x := by rw [h, hx4]
  have h129 : t ^ 12 = t ^ 3 * t ^ 9 := by ring
  have hpos : 0 < t ^ 12 - x := by nlinarith
  have hy2 : 2 ≤ y := by
    by_contra hc
    push Not at hc
    have := cube_sub_self_nonpos (y := y) (by omega)
    omega
  have hexp : (t ^ 4 + 1) ^ 3 - (t ^ 4 + 1) = t ^ 12 + 3 * t ^ 8 + 2 * t ^ 4 := by ring
  have hlow : (t ^ 4) ^ 3 - t ^ 4 < t ^ 12 - x := by rw [← h12]; linarith
  have hhigh : t ^ 12 - x < (t ^ 4 + 1) ^ 3 - (t ^ 4 + 1) := by rw [hexp]; nlinarith
  rcases le_or_gt y (t ^ 4) with hc | hc
  · have := cube_sub_self_mono (a := y) (b := t ^ 4) (by omega) hc
    omega
  · have := cube_sub_self_mono (a := t ^ 4 + 1) (b := y) (by nlinarith) (by omega)
    omega

/-- **Proposition 1.** If `(x, y)` is an integer solution of `y³ - y = x⁴ - x` and `|x|` is a
perfect cube, then `x ∈ {0, 1}` and `y ∈ {-1, 0, 1}`. -/
theorem prop_one {x y t : ℤ} (ht : 0 ≤ t) (hx : x = t ^ 3 ∨ x = -t ^ 3)
    (h : y ^ 3 - y = x ^ 4 - x) : (x = 0 ∨ x = 1) ∧ (y = -1 ∨ y = 0 ∨ y = 1) := by
  rcases lt_or_ge t 2 with hlt | hge
  · interval_cases t
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, or_self] at hx
      subst hx
      exact ⟨Or.inl rfl, cube_sub_self_eq_zero (by linarith [h])⟩
    · norm_num at hx
      rcases hx with rfl | rfl
      · exact ⟨Or.inr rfl, cube_sub_self_eq_zero (by linarith [h])⟩
      · exfalso
        norm_num at h
        rcases le_or_gt y 1 with hc | hc
        · have := cube_sub_self_nonpos (y := y) hc
          omega
        · have := cube_sub_self_mono (a := 2) (b := y) (by norm_num) (by omega)
          norm_num at this
          omega
  · exact (no_solution_of_two_le x y t hge hx h).elim

/-! ### A verified exhaustive check in a small range

The paper does not claim that the six displayed points exhaust the solution set.  We do verify,
by an exhaustive machine check, that they are the only solutions with `|x| ≤ 4`. -/

set_option maxRecDepth 10000 in
private lemma small_range_check :
    ∀ p ∈ (Finset.Icc (-4 : ℤ) 4) ×ˢ (Finset.Icc (-40 : ℤ) 40),
      p.2 ^ 3 - p.2 = p.1 ^ 4 - p.1 →
        p ∈ ({(0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)} : Finset (ℤ × ℤ)) := by
  decide

/-- The six displayed points are the only integer solutions with `|x| ≤ 4`. -/
theorem solutions_with_small_x {x y : ℤ} (hx : |x| ≤ 4) (h : y ^ 3 - y = x ^ 4 - x) :
    (x, y) ∈ ({(0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)} : Finset (ℤ × ℤ)) := by
  rw [abs_le] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hb1 : x ^ 4 - x ≤ 260 := by interval_cases x <;> norm_num
  have hb2 : -260 ≤ x ^ 4 - x := by interval_cases x <;> norm_num
  have hy1 : -40 ≤ y := by
    by_contra hc
    push Not at hc
    have hm := cube_sub_self_mono (a := 41) (b := -y) (by norm_num) (by omega)
    have hodd : (-y) ^ 3 - (-y) = -(y ^ 3 - y) := by ring
    rw [hodd, h] at hm
    norm_num at hm
    omega
  have hy2 : y ≤ 40 := by
    by_contra hc
    push Not at hc
    have hm := cube_sub_self_mono (a := 41) (b := y) (by norm_num) (by omega)
    rw [h] at hm
    norm_num at hm
    omega
  exact small_range_check (x, y) (by simp [Finset.mem_Icc, hx1, hx2, hy1, hy2]) h

/-! ## 2. Irreducibility of `F(x,y) = y³ - y - x⁴ + x` over `ℂ`

We view `F` as an element of `ℂ[x][y]`, which is the usual identification of the polynomial
ring in two variables. -/

section Irreducibility

open Polynomial

/-- The affine equation, as a monic cubic in `y` over `ℂ[x]`. -/
noncomputable def Fcurve : (Polynomial ℂ)[X] :=
  X ^ 3 - X - C (Polynomial.X ^ 4 - Polynomial.X)

lemma Fcurve_monic : Fcurve.Monic := by
  unfold Fcurve; monicity!

lemma Fcurve_natDegree : Fcurve.natDegree = 3 := by
  unfold Fcurve; compute_degree!

/-- No polynomial `p ∈ ℂ[x]` satisfies `p³ - p = x⁴ - x`: degrees cannot match, since
`3 ∤ 4`. -/
lemma no_polynomial_root {p : Polynomial ℂ} :
    p ^ 3 - p ≠ Polynomial.X ^ 4 - Polynomial.X := by
  intro h
  have hrhs : (Polynomial.X ^ 4 - Polynomial.X : Polynomial ℂ).natDegree = 4 := by
    compute_degree!
  rcases eq_or_ne p.natDegree 0 with h0 | h0
  · have hle := Polynomial.natDegree_sub_le (p ^ 3) p
    rw [h, hrhs, natDegree_pow, h0] at hle
    omega
  · have h1 : p.natDegree < (p ^ 3).natDegree := by rw [natDegree_pow]; omega
    have h2 := Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1
    rw [h, hrhs, natDegree_pow] at h2
    omega

/-- **Irreducibility.** `F(x,y) = y³ - y - x⁴ + x` is irreducible over `ℂ`. -/
theorem Fcurve_irreducible : Irreducible Fcurve := by
  rw [Fcurve_monic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℂ)]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [Finset.mem_Icc, Fcurve_monic.natDegree_map, Fcurve_natDegree]
  · intro r hr
    -- a root in `ℂ(x)` would be integral over `ℂ[x]`, hence a polynomial
    have hint : IsIntegral (Polynomial ℂ) r :=
      ⟨Fcurve, Fcurve_monic, by rw [← Polynomial.eval_map]; exact hr⟩
    obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [IsRoot, ← hp, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hr
    have key : Polynomial.eval p Fcurve = 0 :=
      RatFunc.algebraMap_injective ℂ (by simpa using hr)
    simp only [Fcurve, eval_sub, eval_pow, eval_X, eval_C] at key
    exact no_polynomial_root (p := p) (by linear_combination key)

end Irreducibility

/-! ## 3. The projective quartic and its smoothness -/

section Projective

open MvPolynomial

/-- The homogenization `H(X,Y,Z) = Y³Z - YZ³ - X⁴ + XZ³` of the affine equation. -/
noncomputable def Hquartic : MvPolynomial (Fin 3) ℚ :=
  (X 1) ^ 3 * (X 2) - (X 1) * (X 2) ^ 3 - (X 0) ^ 4 + (X 0) * (X 2) ^ 3

theorem Hquartic_isHomogeneous : Hquartic.IsHomogeneous 4 :=
  ((((isHomogeneous_X ℚ 1).pow 3).mul (isHomogeneous_X ℚ 2)).sub
      ((isHomogeneous_X ℚ 1).mul ((isHomogeneous_X ℚ 2).pow 3))).sub
        ((isHomogeneous_X ℚ 0).pow 4) |>.add
          ((isHomogeneous_X ℚ 0).mul ((isHomogeneous_X ℚ 2).pow 3))

@[simp] lemma aeval_Hquartic (z : Fin 3 → ℂ) :
    (aeval z) Hquartic = z 1 ^ 3 * z 2 - z 1 * z 2 ^ 3 - z 0 ^ 4 + z 0 * z 2 ^ 3 := by
  simp [Hquartic]

@[simp] lemma aeval_pderiv_zero (z : Fin 3 → ℂ) :
    (aeval z) (pderiv 0 Hquartic) = -4 * z 0 ^ 3 + z 2 ^ 3 := by
  simp [Hquartic]

@[simp] lemma aeval_pderiv_one (z : Fin 3 → ℂ) :
    (aeval z) (pderiv 1 Hquartic) = 3 * z 1 ^ 2 * z 2 - z 2 ^ 3 := by
  simp [Hquartic]; ring

@[simp] lemma aeval_pderiv_two (z : Fin 3 → ℂ) :
    (aeval z) (pderiv 2 Hquartic) = z 1 ^ 3 - 3 * z 1 * z 2 ^ 2 + 3 * z 0 * z 2 ^ 2 := by
  simp [Hquartic]; ring

/-- The algebraic heart of the smoothness computation: the system
`H = H_X = H_Y = H_Z = 0` has only the trivial solution over `ℂ`. -/
lemma no_nontrivial_singular_point (a b c : ℂ)
    (hz : b ^ 3 * c - b * c ^ 3 - a ^ 4 + a * c ^ 3 = 0)
    (e0 : -4 * a ^ 3 + c ^ 3 = 0)
    (e1 : 3 * b ^ 2 * c - c ^ 3 = 0)
    (e2 : b ^ 3 - 3 * b * c ^ 2 + 3 * a * c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases hc : c = 0
  · -- on the line at infinity the curve meets only `[0 : 1 : 0]`, where `H_Z = Y³ ≠ 0`
    subst hc
    refine ⟨?_, ?_, rfl⟩
    · exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination -e0 / 4)
    · exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination e2)
  · -- in the affine chart `Z = 1` a singular point would need `y² = 1/3`, `x³ = 1/4`
    exfalso
    have hb2 : 3 * b ^ 2 = c ^ 2 := by
      have h : c * (3 * b ^ 2 - c ^ 2) = 0 := by linear_combination e1
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hc
      · exact sub_eq_zero.mp h
    have ha3 : c ^ 3 = 4 * a ^ 3 := by linear_combination e0
    -- feeding these back into `H = 0` gives `9x = 8y`
    have h98 : 9 * a = 8 * b := by
      have h : c ^ 3 * (9 * a - 8 * b) = 0 := by
        linear_combination 12 * hz - 4 * b * c * hb2 - 3 * a * ha3
      rcases mul_eq_zero.1 h with h | h
      · exact (hc (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h)).elim
      · exact sub_eq_zero.mp h
    -- hence `x² = 64/243`, which is incompatible with `x³ = 1/4` since `3¹⁵ ≠ 2²²`
    have h243 : 243 * a ^ 2 = 64 * c ^ 2 := by
      linear_combination 3 * (9 * a + 8 * b) * h98 + 64 * hb2
    have hc6 : c ^ 6 = 16 * a ^ 6 := by linear_combination (c ^ 3 + 4 * a ^ 3) * ha3
    have ha0 : a = 0 := by
      have h : (10154603 : ℂ) * a ^ 6 = 0 := by
        linear_combination (243 ^ 2 * a ^ 4 + 243 * 64 * a ^ 2 * c ^ 2 + 64 ^ 2 * c ^ 4) * h243
          + 64 ^ 3 * hc6
      rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · exact pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h
    exact hc (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by rw [ha3, ha0]; ring))

/-- **Smoothness.** The projective quartic `H = 0` is smooth over `ℂ`: the only common zero of
`H` and of all its partial derivatives is the origin, which is not a point of `ℙ²`.  This
covers both the absence of affine singularities and the smoothness of the unique point at
infinity `[0 : 1 : 0]`. -/
theorem Hquartic_smooth (z : Fin 3 → ℂ) (hz : (aeval z) Hquartic = 0)
    (hd : ∀ i, (aeval z) (pderiv i Hquartic) = 0) : z = 0 := by
  have e0 := hd 0
  have e1 := hd 1
  have e2 := hd 2
  rw [aeval_pderiv_zero] at e0
  rw [aeval_pderiv_one] at e1
  rw [aeval_pderiv_two] at e2
  rw [aeval_Hquartic] at hz
  obtain ⟨ha, hb, hc⟩ := no_nontrivial_singular_point (z 0) (z 1) (z 2) hz e0 e1 e2
  funext i
  fin_cases i <;> simpa using ‹_›

/-! ## 4. Siegel's theorem and the finiteness conclusion

The paper's genus computation (the degree-`3` projection to the `x`-line has eight simple
ramification points plus one point of ramification index `3` at infinity, so
`χ = 3·2 - (8·1 + 2) = -4` and `g = 3`) is not formalized: Mathlib does not provide the genus
of an algebraic curve in a form usable here.  It is not needed either, because the assumed
form of Siegel's theorem below is stated for smooth plane quartics, all of which have genus
`3` by the degree-genus formula; the smoothness of our quartic is proved above. -/

/-- **Siegel's theorem on integral points**, specialized to smooth plane quartics over `ℚ`.

A smooth plane quartic is a geometrically irreducible curve of genus `3 ≥ 1`, so Siegel's
theorem says that it has only finitely many integral points in the affine chart `Z = 1`.

This is the one external input of the paper.  It is *not* proved here, and it is not assumed
as an axiom: it is carried around as an explicit hypothesis of the theorems that use it. -/
def SiegelForSmoothPlaneQuartics : Prop :=
  ∀ P : MvPolynomial (Fin 3) ℚ, P.IsHomogeneous 4 →
    (∀ z : Fin 3 → ℂ, (aeval z) P = 0 → (∀ i, (aeval z) (pderiv i P) = 0) → z = 0) →
      {p : ℤ × ℤ | (eval ![(p.1 : ℚ), (p.2 : ℚ), 1]) P = 0}.Finite

/-- Evaluating the homogenized quartic at `[x : y : 1]` returns the affine equation. -/
lemma eval_Hquartic_int (p : ℤ × ℤ) :
    (eval ![(p.1 : ℚ), (p.2 : ℚ), 1]) Hquartic
      = ((p.2 ^ 3 - p.2 - (p.1 ^ 4 - p.1) : ℤ) : ℚ) := by
  simp [Hquartic]
  ring

/-- The integral points of the affine curve are exactly the integral points of the projective
quartic in the chart `Z = 1`. -/
lemma solution_set_eq :
    {p : ℤ × ℤ | p.2 ^ 3 - p.2 = p.1 ^ 4 - p.1} =
      {p : ℤ × ℤ | (eval ![(p.1 : ℚ), (p.2 : ℚ), 1]) Hquartic = 0} := by
  ext p
  simp only [Set.mem_ofPred_eq, eval_Hquartic_int, Int.cast_eq_zero, sub_eq_zero]

/-- **Theorem 1 of the paper.**  Assuming Siegel's theorem for smooth plane quartics, the set
of integer solutions of `y³ - y = x⁴ - x` is finite.

Hence the assertion that this equation has infinitely many integer solutions is false. -/
theorem y3_sub_y_eq_x4_sub_x_finite_of_siegel (siegel : SiegelForSmoothPlaneQuartics) :
    {p : ℤ × ℤ | p.2 ^ 3 - p.2 = p.1 ^ 4 - p.1}.Finite := by
  rw [solution_set_eq]
  unfold SiegelForSmoothPlaneQuartics at siegel
  exact siegel Hquartic Hquartic_isHomogeneous Hquartic_smooth

/-- Restatement: assuming Siegel's theorem for smooth plane quartics, the equation does **not**
have infinitely many integer solutions. -/
theorem not_infinite_solutions (siegel : SiegelForSmoothPlaneQuartics) :
    ¬ {p : ℤ × ℤ | p.2 ^ 3 - p.2 = p.1 ^ 4 - p.1}.Infinite :=
  Set.not_infinite.mpr (y3_sub_y_eq_x4_sub_x_finite_of_siegel siegel)

end Projective

end CubicQuarticFiniteness
