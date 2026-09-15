import Mathlib

/-!
# A finiteness result for `y ^ 3 + y = x ^ 4 + x`

This file formalizes the note *"A finiteness result for `y³ + y = x⁴ + x`"*.

The paper claims (correctly) that the diophantine equation

  `y ^ 3 + y = x ^ 4 + x`                                                              (1)

has only **finitely many** integer solutions, and proves it by showing that the projective
plane quartic obtained by homogenizing (1) is smooth and geometrically irreducible, hence of
genus `(4 - 1) * (4 - 2) / 2 = 3 > 0`, and then invoking Siegel's theorem on integral points.

The two results quoted from the literature — the **genus formula** for a smooth plane curve and
**Siegel's theorem** — are not proved in the paper, and they are not available in Mathlib either.
They are therefore carried here as explicit hypotheses
(`GenusFormulaHypothesis` and `SiegelHypothesis`) about an abstract genus function; both are
true theorems of algebraic geometry and arithmetic geometry, so the hypotheses are satisfiable
and the formalized implication is exactly the content of the paper.  Everything else — the
geometric verifications of Sections 1–3 of the paper, and the whole elementary section — is
proved unconditionally below.

## Assessment of the paper

The paper's claim is correct, and its proof is valid: the four verification steps (unique smooth
point at infinity, no affine singularities, geometric irreducibility, genus `3`) are all correct,
and Siegel's theorem applies as stated.  The only caveat is the one the paper itself makes: the
argument is not self-contained, since it quotes the genus formula and Siegel's theorem, and it
gives neither an effective bound nor a complete list of the solutions.  (The paper's arithmetic
is also reproduced faithfully here: the substitution in step 2 does give `x = 243/256` together
with `x ^ 2 = -64/243`, an impossibility.)

## Main results

* `projectiveCurve_isHomogeneous` : the homogenization is a quartic form.
* `projectiveCurve_smooth` : the projective curve is smooth over `ℂ` (Sections 1 and 2 of
  the paper: the unique point at infinity is smooth, and there are no affine singularities).
* `affineCurve_irreducible` : the affine curve is geometrically irreducible.
* `finite_integer_solutions` : **Theorem 1** — granting the genus formula and Siegel's theorem,
  equation (1) has only finitely many integer solutions.
* `cube_add_self_strictMono`, `solutions_with_small_x`, `solutions_with_cube_x` : the
  unconditional elementary section of the paper.  In particular the only integer solutions with
  `x` a perfect cube are `(-1, 0)`, `(0, 0)` and `(1, 1)`.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Y3PlusY

/-! ## Part I. The elementary section (unconditional) -/

/-- `h(u) = u ^ 3 + u` is strictly increasing on `ℤ`. -/
theorem cube_add_self_strictMono : StrictMono (fun u : ℤ => u ^ 3 + u) := by
  intro a b hab
  simp only
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- For every integer `x` one has `x ^ 4 + x ≥ 0`; hence any integer solution of (1) has
`y ≥ 0`. -/
theorem solution_y_nonneg (x y : ℤ) (h : y ^ 3 + y = x ^ 4 + x) : 0 ≤ y := by
  have hx : 0 ≤ x ^ 4 + x := by
    rcases le_or_gt 0 x with hx | hx
    · positivity
    · nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x, sq_nonneg (x + 1)]
  by_contra hy
  rw [not_le] at hy
  have : y ^ 3 + y < 0 := by nlinarith [sq_nonneg y]
  omega

/-- The solutions of (1) with `|x| ≤ 1`. -/
theorem solutions_with_small_x (x y : ℤ) (hx : |x| ≤ 1) (h : y ^ 3 + y = x ^ 4 + x) :
    (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
  have hinj := cube_add_self_strictMono.injective
  have hx' : x = -1 ∨ x = 0 ∨ x = 1 := by
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  rcases hx' with rfl | rfl | rfl
  · left
    refine ⟨rfl, hinj (a₁ := y) (a₂ := 0) ?_⟩
    simpa using h
  · right; left
    refine ⟨rfl, hinj (a₁ := y) (a₂ := 0) ?_⟩
    simpa using h
  · right; right
    refine ⟨rfl, hinj (a₁ := y) (a₂ := 1) ?_⟩
    simp only
    norm_num at h ⊢
    omega

/-- The key sandwich: if `y ^ 3 + y = q ^ 3 + c` with `16 ≤ q` and `-q ≤ c < q`, then
`h(q - 1) < h(y) < h(q)`, which is impossible because no integer lies strictly between
`q - 1` and `q`. -/
theorem no_solution_of_sandwich (y q c : ℤ) (hq : 16 ≤ q) (h1 : c < q) (h2 : -q ≤ c)
    (h : y ^ 3 + y = q ^ 3 + c) : False := by
  have hA : y ^ 3 + y < q ^ 3 + q := by omega
  have hB : (q - 1) ^ 3 + (q - 1) < y ^ 3 + y := by nlinarith
  have e1 : y < q := by
    exact cube_add_self_strictMono.lt_iff_lt.mp hA
  have e2 : q - 1 < y := by
    exact cube_add_self_strictMono.lt_iff_lt.mp hB
  omega

/-- **Elementary proposition.** The only integer solutions of (1) for which `x` is a perfect
cube are `(-1, 0)`, `(0, 0)` and `(1, 1)`. -/
theorem solutions_with_cube_x (t y : ℤ) (h : y ^ 3 + y = (t ^ 3) ^ 4 + t ^ 3) :
    (t = -1 ∧ y = 0) ∨ (t = 0 ∧ y = 0) ∨ (t = 1 ∧ y = 1) := by
  rcases le_or_gt 2 |t| with ht | ht
  · exfalso
    rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
    · have ht2 : 2 ≤ t := by omega
      have hp : 0 < t ^ 3 := by positivity
      have h16 : (16 : ℤ) ≤ t ^ 4 := by
        have := pow_le_pow_left₀ (show (0:ℤ) ≤ 2 by norm_num) ht2 4
        norm_num at this ⊢
        linarith
      refine no_solution_of_sandwich y (t ^ 4) (t ^ 3) h16 (by nlinarith) (by nlinarith) ?_
      rw [h]; ring
    · obtain ⟨s, rfl⟩ : ∃ s, t = -s := ⟨-t, by ring⟩
      have hs : 2 ≤ s := by rcases abs_cases (-s) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hp : 0 < s ^ 3 := by positivity
      have h16 : (16 : ℤ) ≤ s ^ 4 := by
        have := pow_le_pow_left₀ (show (0:ℤ) ≤ 2 by norm_num) hs 4
        norm_num at this ⊢
        linarith
      refine no_solution_of_sandwich y (s ^ 4) (-s ^ 3) h16 (by nlinarith) (by nlinarith) ?_
      rw [h]; ring
  · have ht' : t = -1 ∨ t = 0 ∨ t = 1 := by
      rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    have habs : |t ^ 3| ≤ 1 := by
      rcases ht' with rfl | rfl | rfl <;> norm_num
    have := solutions_with_small_x (t ^ 3) y habs h
    rcases ht' with rfl | rfl | rfl <;> norm_num at this ⊢ <;> omega

/-- For `|x| ≥ 2`, every integer solution of (1) satisfies `y > |x|`. -/
theorem solution_y_gt_abs_x (x y : ℤ) (hx : 2 ≤ |x|) (h : y ^ 3 + y = x ^ 4 + x) : |x| < y := by
  have hx4 : x ^ 4 = |x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hxge : -|x| ≤ x := neg_abs_le x
  have hlt : |x| ^ 3 + |x| < y ^ 3 + y := by
    rw [h, hx4]
    have e1 : 2 * |x| ^ 2 ≤ |x| ^ 3 := by nlinarith
    have e2 : 2 * |x| ≤ |x| ^ 2 := by nlinarith
    have e3 : 2 * |x| ^ 3 ≤ |x| ^ 4 := by nlinarith
    linarith
  exact cube_add_self_strictMono.lt_iff_lt.mp hlt

/-- The three small solutions really are solutions. -/
theorem three_solutions :
    ((0:ℤ) ^ 3 + 0 = (-1:ℤ) ^ 4 + (-1)) ∧ ((0:ℤ) ^ 3 + 0 = (0:ℤ) ^ 4 + 0) ∧
      ((1:ℤ) ^ 3 + 1 = (1:ℤ) ^ 4 + 1) := by
  norm_num

/-! ## Part II. The curve, its smoothness and its irreducibility (unconditional) -/

/-- The affine curve `f(x, y) = y ^ 3 + y - x ^ 4 - x`, written as a polynomial in `y` whose
coefficients are polynomials in `x`. -/
noncomputable def affineCurve : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 3 + Polynomial.X - Polynomial.C (Polynomial.X ^ 4 + Polynomial.X)

/-- Base change of a bivariate integer polynomial to `ℂ`. -/
noncomputable def toComplex (g : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℂ) :=
  g.map (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The value of a bivariate polynomial `g ∈ R[x][y]` at the point `(a, b)`. -/
noncomputable def bival {R : Type*} [CommRing R] (g : Polynomial (Polynomial R)) (a b : R) : R :=
  Polynomial.eval b (Polynomial.map (Polynomial.evalRingHom a) g)

@[simp]
theorem bival_affineCurve (a b : ℤ) : bival affineCurve a b = b ^ 3 + b - (a ^ 4 + a) := by
  simp [bival, affineCurve]

theorem toComplex_affineCurve :
    toComplex affineCurve =
      Polynomial.X ^ 3 + Polynomial.X - Polynomial.C (Polynomial.X ^ 4 + Polynomial.X) := by
  simp [toComplex, affineCurve]

@[simp]
theorem bival_toComplex_affineCurve (a b : ℂ) :
    bival (toComplex affineCurve) a b = b ^ 3 + b - (a ^ 4 + a) := by
  rw [toComplex_affineCurve]
  simp [bival]

/-- The homogenization `F(X, Y, Z) = Y³Z + YZ³ - X⁴ - XZ³` of the affine curve, over `ℂ`. -/
noncomputable def projectiveCurve : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 2 ^ 3
    - MvPolynomial.X 0 ^ 4 - MvPolynomial.X 0 * MvPolynomial.X 2 ^ 3

/-- `F` is a form of degree `4`. -/
theorem projectiveCurve_isHomogeneous : projectiveCurve.IsHomogeneous 4 := by
  unfold projectiveCurve
  exact ((((MvPolynomial.isHomogeneous_X _ _).pow 3).mul (MvPolynomial.isHomogeneous_X _ _)).add
      ((MvPolynomial.isHomogeneous_X _ _).mul ((MvPolynomial.isHomogeneous_X _ _).pow 3))).sub
        ((MvPolynomial.isHomogeneous_X _ _).pow 4) |>.sub
          ((MvPolynomial.isHomogeneous_X _ _).mul ((MvPolynomial.isHomogeneous_X _ _).pow 3))

theorem eval_pderiv_zero (p : Fin 3 → ℂ) :
    MvPolynomial.eval p (MvPolynomial.pderiv 0 projectiveCurve) = -4 * p 0 ^ 3 - p 2 ^ 3 := by
  simp [projectiveCurve, MvPolynomial.pderiv_X]

theorem eval_pderiv_one (p : Fin 3 → ℂ) :
    MvPolynomial.eval p (MvPolynomial.pderiv 1 projectiveCurve) =
      3 * p 1 ^ 2 * p 2 + p 2 ^ 3 := by
  simp [projectiveCurve, MvPolynomial.pderiv_X]
  ring

theorem eval_pderiv_two (p : Fin 3 → ℂ) :
    MvPolynomial.eval p (MvPolynomial.pderiv 2 projectiveCurve) =
      p 1 ^ 3 + 3 * p 1 * p 2 ^ 2 - 3 * p 0 * p 2 ^ 2 := by
  simp [projectiveCurve, MvPolynomial.pderiv_X]
  ring

/-- Step 2 of the paper: the affine gradient equations have no common complex solution. -/
theorem no_affine_singularity (x y : ℂ) (h1 : 4 * x ^ 3 = -1) (h2 : 3 * y ^ 2 = -1)
    (h3 : y ^ 3 + 3 * y - 3 * x = 0) : False := by
  have hy2 : y ^ 2 = -1 / 3 := by linear_combination h2 / 3
  have hx3 : x ^ 3 = -1 / 4 := by linear_combination h1 / 4
  have hxy : y = 9 / 8 * x := by linear_combination (3 / 8) * h3 - (3 / 8) * y * hy2
  have hx2 : x ^ 2 = -64 / 243 := by
    rw [hxy] at hy2; linear_combination (64 / 81) * hy2
  have hx : x = 243 / 256 := by
    have h : x * x ^ 2 = -1 / 4 := by linear_combination hx3
    rw [hx2] at h
    linear_combination (-243 / 64) * h
  rw [hx] at hx2
  norm_num at hx2

/-- A projective plane curve `G = 0` is smooth if the gradient of `G` is nonzero at every
point of the curve (the point being given by a nonzero triple of homogeneous coordinates). -/
def IsSmoothProjectivePlaneCurve (G : MvPolynomial (Fin 3) ℂ) : Prop :=
  ∀ p : Fin 3 → ℂ, p ≠ 0 → MvPolynomial.eval p G = 0 →
    ∃ i, MvPolynomial.eval p (MvPolynomial.pderiv i G) ≠ 0

/-- **Steps 1 and 2 of the paper.** The projective quartic `F = 0` is smooth over `ℂ`. -/
theorem projectiveCurve_smooth : IsSmoothProjectivePlaneCurve projectiveCurve := by
  intro p hp _
  by_contra hcon
  have hgrad : ∀ i, MvPolynomial.eval p (MvPolynomial.pderiv i projectiveCurve) = 0 := by
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  have hX : -4 * p 0 ^ 3 - p 2 ^ 3 = 0 := by
    rw [← eval_pderiv_zero p]; exact hgrad 0
  have hY : 3 * p 1 ^ 2 * p 2 + p 2 ^ 3 = 0 := by
    rw [← eval_pderiv_one p]; exact hgrad 1
  have hZ : p 1 ^ 3 + 3 * p 1 * p 2 ^ 2 - 3 * p 0 * p 2 ^ 2 = 0 := by
    rw [← eval_pderiv_two p]; exact hgrad 2
  rcases eq_or_ne (p 2) 0 with hz | hz
  · -- the point at infinity: `Z = 0` forces `X = 0` and `Y = 0`
    rw [hz] at hX hZ
    have hx0 : p 0 = 0 := by
      have : p 0 ^ 3 = 0 := by linear_combination -hX / 4
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    have hy0 : p 1 = 0 := by
      rw [hx0] at hZ
      have : p 1 ^ 3 = 0 := by linear_combination hZ
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    exact hp (funext fun i => by fin_cases i <;> simpa using ‹_›)
  · -- an affine singularity, dehomogenized by `x = X / Z`, `y = Y / Z`
    refine no_affine_singularity (p 0 / p 2) (p 1 / p 2) ?_ ?_ ?_
    · field_simp
      linear_combination -hX
    · have hY' : 3 * p 1 ^ 2 + p 2 ^ 2 = 0 := by
        rcases mul_eq_zero.mp (show p 2 * (3 * p 1 ^ 2 + p 2 ^ 2) = 0 by linear_combination hY)
          with h | h
        · exact absurd h hz
        · exact h
      field_simp
      linear_combination hY'
    · field_simp
      linear_combination hZ

/-- There is no `r ∈ ℂ[x]` with `r ^ 3 + r = x ^ 4 + x`: comparing degrees, `3 ∤ 4`. -/
theorem no_polynomial_root (r : Polynomial ℂ)
    (h : r ^ 3 + r = Polynomial.X ^ 4 + Polynomial.X) : False := by
  have hRHS : (Polynomial.X ^ 4 + Polynomial.X : Polynomial ℂ).natDegree = 4 := by
    compute_degree!
  rcases Nat.eq_zero_or_pos r.natDegree with h0 | hpos
  · have hle : (r ^ 3 + r).natDegree ≤ 0 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp [Polynomial.natDegree_pow, h0]
    rw [h, hRHS] at hle
    omega
  · have h3 : (r ^ 3).natDegree = 3 * r.natDegree := by simp [Polynomial.natDegree_pow]
    have hlt : r.natDegree < (r ^ 3).natDegree := by rw [h3]; omega
    have hdeg : (r ^ 3 + r).natDegree = 3 * r.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]; exact h3
    rw [h, hRHS] at hdeg
    omega

/-- **Step 3 of the paper.** The affine curve is geometrically irreducible: as a monic cubic in
`y` over `ℂ[x]` it has no root in `ℂ[x]`, by the degree argument above. -/
theorem affineCurve_irreducible : Irreducible (toComplex affineCurve) := by
  rw [toComplex_affineCurve]
  have hm : (Polynomial.X ^ 3 + Polynomial.X -
      Polynomial.C (Polynomial.X ^ 4 + Polynomial.X) : Polynomial (Polynomial ℂ)).Monic := by
    monicity!
  have hd : (Polynomial.X ^ 3 + Polynomial.X -
      Polynomial.C (Polynomial.X ^ 4 + Polynomial.X) :
        Polynomial (Polynomial ℂ)).natDegree = 3 := by
    compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hm.ne_zero] at hr
  refine no_polynomial_root r ?_
  have hr' := hr
  simp [Polynomial.IsRoot] at hr'
  linear_combination hr'

/-- A sanity check showing that smoothness, as formalized above, has content: the curve
`Y³Z = X⁴`, which is the singular model considered in the paper's discussion, is *not* smooth
(the point `[0 : 0 : 1]` is a singular point). -/
theorem not_smooth_singular_model :
    ¬ IsSmoothProjectivePlaneCurve
        (MvPolynomial.X 1 ^ 3 * MvPolynomial.X 2 - MvPolynomial.X 0 ^ 4) := by
  intro hsm
  obtain ⟨i, hi⟩ := hsm ![0, 0, 1] (by intro hzero; simpa using congrFun hzero 2) (by simp)
  refine hi ?_
  fin_cases i <;> simp [MvPolynomial.pderiv_X]

/-! ## Part III. Theorem 1, granting the genus formula and Siegel's theorem -/

/-- `G` is the projective closure, as a plane curve of degree `d`, of the affine curve `g`. -/
def IsProjectiveClosure (g : Polynomial (Polynomial ℤ)) (G : MvPolynomial (Fin 3) ℂ)
    (d : ℕ) : Prop :=
  G.IsHomogeneous d ∧
    ∀ x y : ℂ, MvPolynomial.eval ![x, y, 1] G = bival (toComplex g) x y

/-- **The genus formula, quoted (not proved) by the paper.**  If the affine curve `g` has a
smooth, geometrically irreducible projective closure of degree `d ≥ 3`, then the genus of
(the smooth projective model of) `g` is `(d - 1) * (d - 2) / 2`. -/
def GenusFormulaHypothesis (genus : Polynomial (Polynomial ℤ) → ℕ) : Prop :=
  ∀ (g : Polynomial (Polynomial ℤ)) (G : MvPolynomial (Fin 3) ℂ) (d : ℕ), 3 ≤ d →
    IsProjectiveClosure g G d → IsSmoothProjectivePlaneCurve G → Irreducible (toComplex g) →
      genus g = (d - 1) * (d - 2) / 2

/-- **Siegel's theorem, quoted (not proved) by the paper.**  An affine geometrically
irreducible curve over `ℚ` whose smooth projective completion has positive genus has only
finitely many integer points in the given affine embedding. -/
def SiegelHypothesis (genus : Polynomial (Polynomial ℤ) → ℕ) : Prop :=
  ∀ g : Polynomial (Polynomial ℤ), Irreducible (toComplex g) → 0 < genus g →
    {p : ℤ × ℤ | bival g p.1 p.2 = 0}.Finite

theorem projectiveCurve_isProjectiveClosure :
    IsProjectiveClosure affineCurve projectiveCurve 4 := by
  refine ⟨projectiveCurve_isHomogeneous, fun x y => ?_⟩
  rw [bival_toComplex_affineCurve]
  simp [projectiveCurve]
  ring

/-- **Theorem 1.**  Granting the genus formula and Siegel's theorem, the equation
`y ^ 3 + y = x ^ 4 + x` has only finitely many integer solutions. -/
theorem finite_integer_solutions (genus : Polynomial (Polynomial ℤ) → ℕ)
    (hgenus : GenusFormulaHypothesis genus) (hsiegel : SiegelHypothesis genus) :
    {p : ℤ × ℤ | p.2 ^ 3 + p.2 = p.1 ^ 4 + p.1}.Finite := by
  have hg : genus affineCurve = 3 :=
    hgenus affineCurve projectiveCurve 4 (by norm_num) projectiveCurve_isProjectiveClosure
      projectiveCurve_smooth affineCurve_irreducible
  have hfin := hsiegel affineCurve affineCurve_irreducible (by omega)
  have hset : {p : ℤ × ℤ | p.2 ^ 3 + p.2 = p.1 ^ 4 + p.1} =
      {p : ℤ × ℤ | bival affineCurve p.1 p.2 = 0} := by
    ext p
    simp [sub_eq_zero]
  rw [hset]
  exact hfin

end Y3PlusY
