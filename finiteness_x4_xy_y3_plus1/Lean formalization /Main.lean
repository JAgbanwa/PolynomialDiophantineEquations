import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Finiteness of the integer solutions of `x^4 + x*y + y^3 + 1 = 0`

This file formalizes the paper *Finiteness of the integer solutions of `x⁴ + xy + y³ + 1 = 0`*.

Assessment of the paper: its mathematics is correct.  Every algebraic computation it makes
checks out (they are all reproved from scratch below), and its two external inputs — the genus
formula for a smooth plane curve and Faltings' theorem — are genuine theorems applied to a
situation in which their hypotheses have been verified.  The claim that
`x^4 + x*y + y^3 + 1 = 0` has only finitely many rational, hence only finitely many integer,
solutions is therefore true, and the proof is unconditional (though not self-contained).

The mathematical content of the paper is:

* Section 2: the polynomial `f(x,y) = x^4 + x*y + y^3 + 1` is irreducible over `ℂ`
  (`cubicInY_irreducible`, `quartic_irreducible`);
* Section 3: the projective plane quartic `F = X^4 + X*Y*Z^2 + Y^3*Z + Z^4` is smooth over `ℂ`
  (`quarticForm_smooth`), the affine part of the computation being
  `no_affine_singular_point`;
* Section 4: a smooth plane quartic has genus `3`, so Faltings' theorem gives finiteness of the
  set of rational points; two explicit solutions are exhibited.

Faltings' theorem (and the genus formula for a smooth plane curve) are *not* available in
Mathlib, and the paper itself uses them as black boxes.  They are therefore packaged here into
the single explicit hypothesis `FaltingsSmoothPlaneCurves`, which is a standard (true, but here
unproved) statement about smooth plane curves of degree at least `4`.  Every other step of the
paper is proved unconditionally below.
-/

namespace QuarticFiniteness

/-! ## Section 2: irreducibility of the affine quartic -/

section Irreducibility

open Polynomial

/-- No polynomial `s ∈ ℂ[x]` satisfies `s^3 + x*s + x^4 + 1 = 0`: if `deg s ≤ 1` the term `x^4`
dominates, and if `deg s ≥ 2` the term `s^3` dominates.  This is the degree computation of
Section 2 of the paper. -/
theorem no_poly_root (s : ℂ[X]) :
    s ^ 3 + Polynomial.X * s + (Polynomial.X ^ 4 + 1) ≠ 0 := by
  intro h
  rcases eq_or_ne s 0 with rfl | hs
  · have := congrArg (fun p : ℂ[X] => p.coeff 0) h
    simp at this
  · set d := s.natDegree with hd
    have hXs : (Polynomial.X * s).natDegree = d + 1 := by
      rw [natDegree_mul X_ne_zero hs, natDegree_X]; omega
    rcases Nat.lt_or_ge d 2 with hle | hgt
    · have h1 : (s ^ 3).coeff 4 = 0 := by
        apply coeff_eq_zero_of_natDegree_lt; rw [natDegree_pow]; omega
      have h2 : (Polynomial.X * s).coeff 4 = 0 := by
        apply coeff_eq_zero_of_natDegree_lt; omega
      have := congrArg (fun p : ℂ[X] => p.coeff 4) h
      simp [h1, h2, coeff_one] at this
    · have hdeg : (s ^ 3).natDegree = 3 * d := by rw [natDegree_pow]
      have h1 : (Polynomial.X * s).coeff (3 * d) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt; omega
      have h2 : ((Polynomial.X : ℂ[X]) ^ 4).coeff (3 * d) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_X_pow]; omega
      have h3 : ((1 : ℂ[X])).coeff (3 * d) = 0 := by
        rw [coeff_one]; simp; omega
      have h4 : (s ^ 3).coeff (3 * d) ≠ 0 := by
        rw [← hdeg, coeff_natDegree]
        exact leadingCoeff_ne_zero.2 (pow_ne_zero 3 hs)
      have := congrArg (fun p : ℂ[X] => p.coeff (3 * d)) h
      simp [h1, h2, h3] at this
      exact h4 this

/-- The quartic, viewed as a monic cubic in `y` over the ring `ℂ[x]`. -/
noncomputable def cubicInY : (ℂ[X])[X] :=
  Polynomial.X ^ 3 +
    (C (Polynomial.X : ℂ[X]) * Polynomial.X + C ((Polynomial.X : ℂ[X]) ^ 4 + 1))

theorem cubicInY_monic : cubicInY.Monic := by
  have hlt : (C (Polynomial.X : ℂ[X]) * Polynomial.X + C ((Polynomial.X : ℂ[X]) ^ 4 + 1)).degree
      < ((Polynomial.X : (ℂ[X])[X]) ^ 3).degree := by
    rw [degree_X_pow]
    apply lt_of_le_of_lt (degree_add_le _ _)
    simp only [max_lt_iff]
    refine ⟨?_, lt_of_le_of_lt degree_C_le (by decide)⟩
    apply lt_of_le_of_lt (degree_mul_le _ _)
    exact lt_of_le_of_lt (add_le_add degree_C_le (le_of_eq degree_X)) (by decide)
  exact (monic_X_pow 3).add_of_left hlt

theorem cubicInY_natDegree : cubicInY.natDegree = 3 := by
  unfold cubicInY; compute_degree!

/-- The cubic has no root in the field of rational functions `ℂ(x)`: such a root is integral
over `ℂ[x]`, hence lies in `ℂ[x]` because `ℂ[x]` is integrally closed, and then `no_poly_root`
applies. -/
theorem no_ratfunc_root (r : RatFunc ℂ)
    (h : r ^ 3 + (algebraMap ℂ[X] (RatFunc ℂ) Polynomial.X) * r
      + algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.X ^ 4 + 1) = 0) : False := by
  have hint : IsIntegral ℂ[X] r := ⟨cubicInY, cubicInY_monic, by
    simp only [cubicInY, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow]
    linear_combination h⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  subst hs
  have hz : (algebraMap ℂ[X] (RatFunc ℂ))
      (s ^ 3 + Polynomial.X * s + (Polynomial.X ^ 4 + 1)) = 0 := by
    simp only [map_add, map_mul, map_pow, map_one] at h ⊢
    linear_combination h
  exact no_poly_root s ((map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).1 hz)

/-- **Section 2 of the paper**, in the form of a monic cubic over `ℂ[x]`: `y^3 + x*y + x^4 + 1`
is irreducible in `ℂ[x][y]`.  By Gauss' lemma this reduces to irreducibility over `ℂ(x)`, where
it follows from the absence of roots (a cubic is reducible iff it has a root). -/
theorem cubicInY_irreducible : Irreducible cubicInY := by
  rw [cubicInY_monic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℂ)]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicInY_monic.natDegree_map, cubicInY_natDegree]; simp
  · intro r hr
    rw [IsRoot, eval_map] at hr
    refine no_ratfunc_root r ?_
    simp only [cubicInY, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow] at hr
    linear_combination hr

/-- The isomorphism `ℂ[x₀] ≃ ℂ[X]` for the one-variable polynomial rings. -/
noncomputable def mvOneEquiv : MvPolynomial (Fin 1) ℂ ≃+* ℂ[X] :=
  ((MvPolynomial.finSuccEquiv ℂ 0).toRingEquiv).trans
    (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)))

/-- The isomorphism `ℂ[x₀, x₁] ≃ ℂ[x][y]`, sending `x₀` to the inner variable `x` and `x₁` to
the outer variable `y`. -/
noncomputable def mvTwoEquiv : MvPolynomial (Fin 2) ℂ ≃+* (ℂ[X])[X] :=
  ((MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv).trans
    (((MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv).trans (Polynomial.mapEquiv mvOneEquiv))

theorem mvOneEquiv_X : mvOneEquiv (MvPolynomial.X 0) = Polynomial.X := by
  simp [mvOneEquiv, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

theorem mvTwoEquiv_X0 : mvTwoEquiv (MvPolynomial.X 0) = C (Polynomial.X : ℂ[X]) := by
  have h : (MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 1)
      = Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  simp [mvTwoEquiv, h, mvOneEquiv_X]

theorem mvTwoEquiv_X1 : mvTwoEquiv (MvPolynomial.X 1) = Polynomial.X := by
  simp [mvTwoEquiv, MvPolynomial.finSuccEquiv_X_zero]

/-- **Section 2 of the paper.**  The affine quartic `x^4 + x*y + y^3 + 1` is irreducible over
`ℂ`, hence the curve it defines is geometrically irreducible. -/
theorem quartic_irreducible :
    Irreducible ((MvPolynomial.X 0 ^ 4 + MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.X 1 ^ 3 + 1 : MvPolynomial (Fin 2) ℂ)) := by
  rw [← MulEquiv.irreducible_iff (f := mvTwoEquiv)]
  have himg : mvTwoEquiv (MvPolynomial.X 0 ^ 4 + MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.X 1 ^ 3 + 1) = cubicInY := by
    simp only [map_add, map_mul, map_pow, map_one, mvTwoEquiv_X0, mvTwoEquiv_X1, cubicInY]
    ring
  rw [himg]
  exact cubicInY_irreducible

end Irreducibility

open MvPolynomial

/-! ## The affine and projective equations -/

/-- The homogeneous quartic form `F(X,Y,Z) = X^4 + X*Y*Z^2 + Y^3*Z + Z^4`, the projective
completion of the affine curve `x^4 + x*y + y^3 + 1 = 0`. -/
noncomputable def quarticForm : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ 4 + X 0 * X 1 * X 2 ^ 2 + X 1 ^ 3 * X 2 + X 2 ^ 4

/-- The dehomogenization `F(x,y,1)`, viewed as a bivariate polynomial over `ℂ`. -/
noncomputable def dehomogenizeC (F : MvPolynomial (Fin 3) ℚ) : MvPolynomial (Fin 2) ℂ :=
  bind₁ ![X 0, X 1, 1] (F.map (algebraMap ℚ ℂ))

@[simp] theorem eval_quarticForm_C (v : Fin 3 → ℂ) :
    eval v (quarticForm.map (algebraMap ℚ ℂ)) =
      v 0 ^ 4 + v 0 * v 1 * v 2 ^ 2 + v 1 ^ 3 * v 2 + v 2 ^ 4 := by
  simp [quarticForm]

theorem eval_pderiv_zero (v : Fin 3 → ℂ) :
    eval v ((pderiv 0 quarticForm).map (algebraMap ℚ ℂ)) = 4 * v 0 ^ 3 + v 1 * v 2 ^ 2 := by
  simp [quarticForm, pderiv_X]; ring

theorem eval_pderiv_one (v : Fin 3 → ℂ) :
    eval v ((pderiv 1 quarticForm).map (algebraMap ℚ ℂ)) = v 0 * v 2 ^ 2 + 3 * v 1 ^ 2 * v 2 := by
  simp [quarticForm, pderiv_X]; ring

theorem eval_pderiv_two (v : Fin 3 → ℂ) :
    eval v ((pderiv 2 quarticForm).map (algebraMap ℚ ℂ)) =
      2 * v 0 * v 1 * v 2 + v 1 ^ 3 + 4 * v 2 ^ 3 := by
  simp [quarticForm, pderiv_X]; ring

/-- The quartic form is homogeneous of degree `4`. -/
theorem quarticForm_isHomogeneous : quarticForm.IsHomogeneous 4 := by
  have h : ∀ i : Fin 3, (X i : MvPolynomial (Fin 3) ℚ).IsHomogeneous 1 := fun i =>
    isHomogeneous_X _ i
  have h4 : ((X 0 : MvPolynomial (Fin 3) ℚ) ^ 4).IsHomogeneous 4 := by simpa using (h 0).pow 4
  have hm : ((X 0 * X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) ℚ)).IsHomogeneous 4 := by
    simpa using ((h 0).mul (h 1)).mul ((h 2).pow 2)
  have h3 : ((X 1 ^ 3 * X 2 : MvPolynomial (Fin 3) ℚ)).IsHomogeneous 4 := by
    simpa using ((h 1).pow 3).mul (h 2)
  have hz : ((X 2 : MvPolynomial (Fin 3) ℚ) ^ 4).IsHomogeneous 4 := by simpa using (h 2).pow 4
  exact ((h4.add hm).add h3).add hz

/-- Dehomogenizing `F` at `Z = 1` gives back the affine quartic. -/
theorem dehomogenizeC_quarticForm :
    dehomogenizeC quarticForm = X 0 ^ 4 + X 0 * X 1 + X 1 ^ 3 + 1 := by
  simp [dehomogenizeC, quarticForm]


/-! ## Section 3: smoothness -/

/-- **The affine smoothness computation of Section 3.**  There is no complex point at which
`f` and both of its partial derivatives vanish. -/
theorem no_affine_singular_point (x y : ℂ) (hf : x ^ 4 + x * y + y ^ 3 + 1 = 0)
    (hx : 4 * x ^ 3 + y = 0) (hy : x + 3 * y ^ 2 = 0) : False := by
  have hy' : y = -4 * x ^ 3 := by linear_combination hx
  subst hy'
  have hx0 : x * (1 + 48 * x ^ 5) = 0 := by linear_combination hy
  rcases mul_eq_zero.1 hx0 with h | h
  · subst h; norm_num at hf
  · have hx5 : x ^ 5 = -(1 / 48) := by linear_combination h / 48
    have h4 : x ^ 4 = 3 / 5 := by linear_combination (-3 / 5) * hf + (-(192 / 5) * x ^ 4) * hx5
    have : ((3 : ℂ) / 5) ^ 5 = (-(1 / 48) : ℂ) ^ 4 := by rw [← h4, ← hx5]; ring
    norm_num at this

/-- **Section 3 of the paper.**  The projective plane quartic `F = 0` is smooth over `ℂ`: the
only common complex zero of `F` and of all its partial derivatives is the origin (which is not a
point of the projective plane). -/
theorem quarticForm_smooth (v : Fin 3 → ℂ) (hF : eval v (quarticForm.map (algebraMap ℚ ℂ)) = 0)
    (hd : ∀ i, eval v ((pderiv i quarticForm).map (algebraMap ℚ ℂ)) = 0) : v = 0 := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  rw [eval_pderiv_zero] at h0
  rw [eval_pderiv_one] at h1
  rw [eval_pderiv_two] at h2
  rw [eval_quarticForm_C] at hF
  by_cases hz : v 2 = 0
  · -- the point at infinity `[0 : 1 : 0]` is not singular
    rw [hz] at hF h2
    have hx : v 0 = 0 := by
      have : v 0 ^ 4 = 0 := by linear_combination hF
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 this
    have hy : v 1 = 0 := by
      have : v 1 ^ 3 = 0 := by linear_combination h2
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this
    funext i
    fin_cases i <;> simpa using ‹_›
  · -- an affine singular point would contradict `no_affine_singular_point`
    exfalso
    have hc : v 0 * v 2 + 3 * v 1 ^ 2 = 0 := by
      have h : v 2 * (v 0 * v 2 + 3 * v 1 ^ 2) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h).resolve_left hz
    refine no_affine_singular_point (v 0 / v 2) (v 1 / v 2) ?_ ?_ ?_
    · field_simp
      linear_combination hF
    · field_simp
      linear_combination h0
    · field_simp
      linear_combination hc

/-! ## Section 4: Faltings' theorem and the finiteness conclusion -/

/-- **Faltings' theorem for smooth plane curves** (used without proof, exactly as in the paper).

If `F` is a form of degree `d ≥ 4` in three variables with rational coefficients whose
dehomogenization is irreducible over `ℂ` and whose complex projective zero locus is smooth (the
only common zero of `F` and all of its partial derivatives is the origin), then the projective
curve `F = 0` is a smooth geometrically irreducible curve of genus `(d-1)(d-2)/2 ≥ 3 ≥ 2` over
`ℚ`, so by Faltings' theorem it has only finitely many rational points; in particular the set of
rational points in the affine chart `Z = 1` is finite.

Neither Faltings' theorem nor the genus formula for smooth plane curves is available in Mathlib,
so this statement is introduced as an explicit hypothesis rather than proved. -/
def FaltingsSmoothPlaneCurves : Prop :=
  ∀ (F : MvPolynomial (Fin 3) ℚ) (d : ℕ), 4 ≤ d → F.IsHomogeneous d →
    Irreducible (dehomogenizeC F) →
    (∀ v : Fin 3 → ℂ, eval v (F.map (algebraMap ℚ ℂ)) = 0 →
        (∀ i, eval v ((pderiv i F).map (algebraMap ℚ ℂ)) = 0) → v = 0) →
    {p : ℚ × ℚ | eval ![p.1, p.2, 1] F = 0}.Finite

/-- **Theorem 1 of the paper.**  Granting Faltings' theorem, the set of *rational* solutions of
`x^4 + x*y + y^3 + 1 = 0` is finite. -/
theorem rational_solutions_finite (hFaltings : FaltingsSmoothPlaneCurves) :
    {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0}.Finite := by
  have h := hFaltings quarticForm 4 le_rfl quarticForm_isHomogeneous
    (by rw [dehomogenizeC_quarticForm]; exact quartic_irreducible)
    (fun v hF hd => quarticForm_smooth v hF hd)
  have hset : {p : ℚ × ℚ | eval ![p.1, p.2, 1] quarticForm = 0} =
      {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0} := by
    ext p
    simp [quarticForm]
  rwa [hset] at h

/-- Granting Faltings' theorem, the set of *integer* solutions of `x^4 + x*y + y^3 + 1 = 0` is
finite; in particular the equation does not have infinitely many integer solutions. -/
theorem integer_solutions_finite (hFaltings : FaltingsSmoothPlaneCurves) :
    {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0}.Finite := by
  have hinj : Function.Injective (fun p : ℤ × ℤ => ((p.1 : ℚ), (p.2 : ℚ))) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq, Int.cast_injective.eq_iff] at h
    simp [h.1, h.2]
  have hsub : {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0} ⊆
      (fun p : ℤ × ℤ => ((p.1 : ℚ), (p.2 : ℚ))) ⁻¹'
        {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0} := by
    rintro ⟨a, b⟩ h
    have h' : ((a : ℚ)) ^ 4 + (a : ℚ) * (b : ℚ) + (b : ℚ) ^ 3 + 1 = 0 := by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℚ)) h
    exact h'
  exact Set.Finite.subset
    ((rational_solutions_finite hFaltings).preimage hinj.injOn) hsub

/-- Granting Faltings' theorem, the claim that the equation has infinitely many integer
solutions is false. -/
theorem not_infinite_integer_solutions (hFaltings : FaltingsSmoothPlaneCurves) :
    ¬ {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0}.Infinite :=
  Set.not_infinite.2 (integer_solutions_finite hFaltings)

/-! ## The two explicit solutions -/

theorem solution_zero :
    ((0 : ℤ), (-1 : ℤ)) ∈ {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0} := by
  norm_num

theorem solution_one :
    ((1 : ℤ), (-1 : ℤ)) ∈ {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 + 1 = 0} := by
  norm_num

end QuarticFiniteness
