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
# The equation `x⁴ + x y + y³ = 1` : finiteness of the solution set

This file formalizes the paper *"The equation x⁴ + xy + y³ = 1: a finiteness result and the
obstruction to infinitude"*.

## Verdict on the paper

The paper's mathematics is correct. The curve really is a smooth plane quartic: the explicit
computations in §2 (the unique point at infinity `[0 : 1 : 0]` with `F_Z = 1`, the absence of
affine singularities via `x⁵ = -1/48`, `x⁴ = -3/5`, `x = 5/144`, and the irreducibility
argument) all check out and are reproved below without any appeal to outside results. The
genus formula then gives genus `3`, and Faltings' theorem gives finiteness of the rational
points, hence of the integer points. So the finiteness conclusion is true and unconditional
(it relies only on established theorems), and the claimed infinitude of solutions is indeed
false. The one caveat, which the paper itself states, is that the proof is not self-contained:
finiteness is *not* proved from scratch, and no explicit bound on the solutions is obtained, so
the argument does not show that the five listed solutions are all of them.

## What the paper does, and what is formalized here

The paper proves, by explicit computation, that the projective plane quartic

`F(X,Y,Z) = X⁴ + X Y Z² + Y³ Z - Z⁴`

is smooth and geometrically irreducible, concludes from the genus formula that its genus is
`(4-1)(4-2)/2 = 3`, and then *invokes* Faltings' theorem to deduce that the set of rational
points is finite. The paper is explicit that the last step is an invocation, not a proof.

Everything in the paper that is an actual computation is proved here unconditionally:

* `QuarticCurve.no_affine_singular_point` — the affine system `f = f_x = f_y = 0` has no
  solution over `ℂ` (this is §2 of the paper, including the arithmetic with `x⁵ = -1/48`
  and `x⁴ = -3/5`);
* `QuarticCurve.eval_at_infinity`, `QuarticCurve.pderivZ_at_infinity` — `Z = 0` meets the
  curve only at `P = [0 : 1 : 0]`, and `F_Z(P) = 1`, so `P` is a smooth point;
* `QuarticCurve.smooth` — the Jacobian criterion: the only common complex zero of the three
  partial derivatives of `F` is the origin, i.e. the projective curve is smooth;
* `QuarticCurve.no_homogeneous_factorization` — `F` admits no factorization over `ℂ` into two
  homogeneous factors of positive degree (the paper's geometric irreducibility argument);
* `QuarticCurve.solutions_with_small_x` — the five integer solutions listed in §4 are exactly
  the integer solutions with `|x| ≤ 1`.

The two general theorems that the paper invokes (the genus formula for smooth plane curves and
Faltings' theorem) are not available in Mathlib and are not proved here. They are packaged into
the single explicit hypothesis `QuarticCurve.FaltingsSmoothPlaneQuartic`, which is a true
theorem of arithmetic geometry (a plane quartic over `ℚ` that is smooth over `ℂ` is
automatically geometrically irreducible, has genus `3`, and Faltings' theorem then bounds its
rational points). The final results

* `QuarticCurve.rational_solutions_finite`
* `QuarticCurve.integer_solutions_finite`
* `QuarticCurve.not_infinite_integer_solutions`

are stated with that hypothesis as an explicit argument.
-/

namespace QuarticCurve

open MvPolynomial

/-! ## The curve -/

/-- The homogeneous quartic `F(X,Y,Z) = X⁴ + X Y Z² + Y³ Z - Z⁴` over `ℚ`, the projective
closure of `x⁴ + x y + y³ - 1 = 0`. -/
noncomputable def Fq : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ 4 + X 0 * X 1 * X 2 ^ 2 + X 1 ^ 3 * X 2 - X 2 ^ 4

/-- The same quartic viewed over `ℂ`. -/
noncomputable def Fc : MvPolynomial (Fin 3) ℂ :=
  X 0 ^ 4 + X 0 * X 1 * X 2 ^ 2 + X 1 ^ 3 * X 2 - X 2 ^ 4

theorem map_Fq : Fq.map (algebraMap ℚ ℂ) = Fc := by
  simp [Fq, Fc]

theorem Fq_isHomogeneous : Fq.IsHomogeneous 4 := by
  unfold Fq
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add
    (MvPolynomial.IsHomogeneous.add ((isHomogeneous_X ℚ 0).pow 4) ?_) ?_)
    ((isHomogeneous_X ℚ 2).pow 4)
  · exact ((isHomogeneous_X ℚ 0).mul (isHomogeneous_X ℚ 1)).mul ((isHomogeneous_X ℚ 2).pow 2)
  · exact ((isHomogeneous_X ℚ 1).pow 3).mul (isHomogeneous_X ℚ 2)

theorem Fc_isHomogeneous : Fc.IsHomogeneous 4 := by
  unfold Fc
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add
    (MvPolynomial.IsHomogeneous.add ((isHomogeneous_X ℂ 0).pow 4) ?_) ?_)
    ((isHomogeneous_X ℂ 2).pow 4)
  · exact ((isHomogeneous_X ℂ 0).mul (isHomogeneous_X ℂ 1)).mul ((isHomogeneous_X ℂ 2).pow 2)
  · exact ((isHomogeneous_X ℂ 1).pow 3).mul (isHomogeneous_X ℂ 2)

theorem Fc_ne_zero : Fc ≠ 0 := by
  intro h
  have h2 := congrArg (eval ![(1 : ℂ), 0, 0]) h
  simp [Fc] at h2

/-- The value of `F` on an affine point `(x, y, 1)`. -/
theorem eval_affine (x y : ℚ) : eval ![x, y, 1] Fq = x ^ 4 + x * y + y ^ 3 - 1 := by
  simp [Fq]

/-- The three partial derivatives of `F`, evaluated at a complex point. -/
theorem aeval_pderiv_zero (v : Fin 3 → ℂ) :
    aeval v (pderiv 0 Fq) = 4 * v 0 ^ 3 + v 1 * v 2 ^ 2 := by
  simp [Fq, pderiv_X]; ring

theorem aeval_pderiv_one (v : Fin 3 → ℂ) :
    aeval v (pderiv 1 Fq) = v 0 * v 2 ^ 2 + 3 * v 1 ^ 2 * v 2 := by
  simp [Fq, pderiv_X]; ring

theorem aeval_pderiv_two (v : Fin 3 → ℂ) :
    aeval v (pderiv 2 Fq) = 2 * v 0 * v 1 * v 2 + v 1 ^ 3 - 4 * v 2 ^ 3 := by
  simp [Fq, pderiv_X]; ring

/-! ## The point at infinity -/

/-- Setting `Z = 0` in `F` gives `X⁴`; hence `P = [0 : 1 : 0]` is the only point of the curve
at infinity. -/
theorem eval_at_infinity (x y : ℂ) : aeval ![x, y, (0 : ℂ)] Fq = x ^ 4 := by
  simp [Fq]

/-- `F_Z(0, 1, 0) = 1`, so the point at infinity `P = [0 : 1 : 0]` is a smooth point. -/
theorem pderivZ_at_infinity : aeval ![(0 : ℂ), 1, 0] (pderiv 2 Fq) = 1 := by
  rw [aeval_pderiv_two]; simp

/-! ## No affine singular point (§2 of the paper) -/

/-- **There are no affine singularities, even complex ones.**
The system `f = 0`, `f_x = 4x³ + y = 0`, `f_y = x + 3y² = 0` has no solution over `ℂ`.
This is the computation of §2: it forces `x⁵ = -1/48` and `x⁴ = -3/5`, hence
`x = x⁵ / x⁴ = 5/144`, whose fourth power is positive. -/
theorem no_affine_singular_point (x y : ℂ) (hf : x ^ 4 + x * y + y ^ 3 - 1 = 0)
    (hfx : 4 * x ^ 3 + y = 0) (hfy : x + 3 * y ^ 2 = 0) : False := by
  have hy1 : y = -4 * x ^ 3 := by linear_combination hfx
  subst hy1
  have hq : x * (1 + 48 * x ^ 5) = 0 := by linear_combination hfy
  have hc : -3 * x ^ 4 - 64 * x ^ 9 - 1 = 0 := by linear_combination hf
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hc
  have h5 : x ^ 5 = -1 / 48 := by
    have h : 1 + 48 * x ^ 5 = 0 := by
      rcases mul_eq_zero.1 hq with h | h
      · exact absurd h hx0
      · exact h
    linear_combination h / 48
  have h4 : x ^ 4 = -3 / 5 := by
    linear_combination (-3 / 5 : ℂ) * hc - (64 * 3 / 5 : ℂ) * x ^ 4 * h5
  have hxv : x = 5 / 144 := by
    linear_combination (-5 / 3 : ℂ) * h5 + (5 / 3 : ℂ) * x * h4
  rw [hxv] at h4
  norm_num at h4

/-! ## Smoothness of the projective curve -/

/-- Auxiliary form of the smoothness statement: if the three partial derivatives of `F` vanish
at `(X, Y, Z)` with `Z ≠ 0`, we obtain an affine singular point, which is impossible. -/
theorem no_singular_point_with_Z_ne_zero (x y z : ℂ) (hz : z ≠ 0)
    (h0 : 4 * x ^ 3 + y * z ^ 2 = 0) (h1 : x * z ^ 2 + 3 * y ^ 2 * z = 0)
    (h2 : 2 * x * y * z + y ^ 3 - 4 * z ^ 3 = 0) : False := by
  -- Euler's identity: `4 F = X F_X + Y F_Y + Z F_Z`, so `F` vanishes too.
  have hF : x ^ 4 + x * y * z ^ 2 + y ^ 3 * z - z ^ 4 = 0 := by
    linear_combination (x / 4) * h0 + (y / 4) * h1 + (z / 4) * h2
  refine no_affine_singular_point (x / z) (y / z) ?_ ?_ ?_
  · have e : (x / z) ^ 4 + (x / z) * (y / z) + (y / z) ^ 3 - 1
        = (x ^ 4 + x * y * z ^ 2 + y ^ 3 * z - z ^ 4) / z ^ 4 := by field_simp
    rw [e, hF, zero_div]
  · have e : 4 * (x / z) ^ 3 + y / z = (4 * x ^ 3 + y * z ^ 2) / z ^ 3 := by field_simp
    rw [e, h0, zero_div]
  · have e : x / z + 3 * (y / z) ^ 2 = (x * z ^ 2 + 3 * y ^ 2 * z) / z ^ 3 := by field_simp
    rw [e, h1, zero_div]

/-- **The projective quartic `C : F = 0` is smooth.**
By the Jacobian criterion this is the statement that the only common complex zero of the three
partial derivatives of `F` is the origin. -/
theorem smooth (v : Fin 3 → ℂ) (hv : ∀ i, aeval v (pderiv i Fq) = 0) : v = 0 := by
  have h0 : 4 * v 0 ^ 3 + v 1 * v 2 ^ 2 = 0 := by rw [← aeval_pderiv_zero]; exact hv 0
  have h1 : v 0 * v 2 ^ 2 + 3 * v 1 ^ 2 * v 2 = 0 := by rw [← aeval_pderiv_one]; exact hv 1
  have h2 : 2 * v 0 * v 1 * v 2 + v 1 ^ 3 - 4 * v 2 ^ 3 = 0 := by
    rw [← aeval_pderiv_two]; exact hv 2
  by_cases hz : v 2 = 0
  · -- On `Z = 0` the equations force `X = 0` and then `Y = 0`.
    have hx : v 0 = 0 := by
      have h : v 0 ^ 3 = 0 := by rw [hz] at h0; linear_combination h0 / 4
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
    have hy : v 1 = 0 := by
      have h : v 1 ^ 3 = 0 := by rw [hz, hx] at h2; linear_combination h2
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
    funext i
    fin_cases i <;> simpa using ‹_›
  · exact (no_singular_point_with_Z_ne_zero (v 0) (v 1) (v 2) hz h0 h1 h2).elim

/-! ## Geometric irreducibility (§2 of the paper) -/

/-- Substitution `(X, Y, Z) ↦ (T, 1, 0)`, i.e. restriction of a form to the line at infinity,
read along the line through the point at infinity `P = [0 : 1 : 0]`. -/
noncomputable def lineAtInfinity : Fin 3 → Polynomial ℂ := ![Polynomial.X, 1, 0]

/-- Restricting a homogeneous form of degree `m` to a line gives a univariate polynomial of
degree at most `m`. -/
theorem natDegree_aeval_le (G : MvPolynomial (Fin 3) ℂ) (m : ℕ) (hG : G.IsHomogeneous m) :
    ((aeval lineAtInfinity) G).natDegree ≤ m := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro d hd
  have h1 : ∀ c : ℂ, ((aeval lineAtInfinity) ((monomial d) c)).natDegree ≤ d 0 := by
    intro c
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp), Fin.prod_univ_three]
    by_cases h2 : d 2 = 0
    · simp only [lineAtInfinity, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        h2, one_pow, mul_one, pow_zero, Matrix.tail_cons, Matrix.head_cons]
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
    · simp [lineAtInfinity, zero_pow h2]
  refine (h1 _).trans ?_
  have hle : (d.sum fun _ e => e) ≤ G.totalDegree := MvPolynomial.le_totalDegree hd
  refine le_trans ?_ (hle.trans hG.totalDegree_le)
  rw [Finsupp.sum_fintype _ _ (by intro i; simp), Fin.sum_univ_three]
  omega

/-- Evaluating the restriction to the line at `T = 0` is evaluation at the point at infinity
`P = [0 : 1 : 0]`. -/
theorem eval_zero_aeval (G : MvPolynomial (Fin 3) ℂ) :
    Polynomial.eval 0 (aeval lineAtInfinity G) = eval ![(0 : ℂ), 1, 0] G := by
  have h : (Polynomial.aeval (0 : ℂ)).comp
      (aeval lineAtInfinity : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] Polynomial ℂ)
      = aeval ![(0 : ℂ), 1, 0] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineAtInfinity]
  have h2 := congrArg (fun f => f G) h
  simp only [AlgHom.coe_comp, Function.comp_apply] at h2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h2

private theorem natDegree_of_associated_X_pow (p : Polynomial ℂ) (r : ℕ) (hp : p ≠ 0)
    (h : Associated p (Polynomial.X ^ r)) : p.natDegree = r := by
  obtain ⟨u, hu⟩ := h
  have h1 := congrArg Polynomial.natDegree hu
  rwa [Polynomial.natDegree_mul hp u.ne_zero,
    Polynomial.natDegree_eq_zero_of_isUnit u.isUnit, add_zero, Polynomial.natDegree_X_pow] at h1

private theorem eval_zero_of_associated_X_pow (p : Polynomial ℂ) (r : ℕ) (hr : 0 < r)
    (h : Associated p (Polynomial.X ^ r)) : Polynomial.eval 0 p = 0 := by
  obtain ⟨u, hu⟩ := h
  have h2 := congrArg (Polynomial.eval 0) hu
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow hr.ne', mul_eq_zero] at h2
  have hu1 : Polynomial.eval 0 (u : Polynomial ℂ) *
      Polynomial.eval 0 (↑u⁻¹ : Polynomial ℂ) = 1 := by
    rw [← Polynomial.eval_mul, ← Units.val_mul]; simp
  rcases h2 with h2 | h2
  · exact h2
  · rw [h2] at hu1; simp at hu1

/-- **The quartic is geometrically irreducible**, in the precise form proved in the paper:
over `ℂ`, `F` admits no factorization `F = G · H` into homogeneous factors of positive degree.

The argument: restricting to `Z = 0` gives `G(X,Y,0) H(X,Y,0) = X⁴`, so each restriction is a
constant times a power of `X` of positive degree; hence both `G` and `H` vanish at the point at
infinity `P = [0 : 1 : 0]`, and the product rule would give `F_Z(P) = 0`, contradicting
`F_Z(P) = 1`. -/
theorem no_homogeneous_factorization (G H : MvPolynomial (Fin 3) ℂ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous n)
    (hFGH : Fc = G * H) : False := by
  have hmn : m + n = 4 := (hG.mul hH).inj_right (hFGH ▸ Fc_isHomogeneous) (hFGH ▸ Fc_ne_zero)
  set g := aeval lineAtInfinity G with hgdef
  set k := aeval lineAtInfinity H with hkdef
  have hgk : g * k = Polynomial.X ^ 4 := by
    rw [hgdef, hkdef, ← map_mul, ← hFGH]; simp [Fc, lineAtInfinity]
  have hprod : g * k ≠ 0 := by rw [hgk]; exact pow_ne_zero _ Polynomial.X_ne_zero
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hprod
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hprod
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (q := g) Polynomial.prime_X 4).1 ⟨k, hgk.symm⟩
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (q := k) Polynomial.prime_X 4).1 ⟨g, by rw [← hgk]; ring⟩
  have hdi : g.natDegree = i := natDegree_of_associated_X_pow g i hg0 hi
  have hdj : k.natDegree = j := natDegree_of_associated_X_pow k j hk0 hj
  have hsum : i + j = 4 := by
    have h : (g * k).natDegree = 4 := by rw [hgk]; simp
    rwa [Polynomial.natDegree_mul hg0 hk0, hdi, hdj] at h
  have him : i ≤ m := hdi ▸ natDegree_aeval_le G m hG
  have hjn : j ≤ n := hdj ▸ natDegree_aeval_le H n hH
  -- Both factors vanish at the point at infinity.
  have hGP : eval ![(0 : ℂ), 1, 0] G = 0 := by
    rw [← eval_zero_aeval, ← hgdef]
    exact eval_zero_of_associated_X_pow g i (by omega) hi
  have hHP : eval ![(0 : ℂ), 1, 0] H = 0 := by
    rw [← eval_zero_aeval, ← hkdef]
    exact eval_zero_of_associated_X_pow k j (by omega) hj
  -- The product rule then kills `F_Z(P)`, which is `1`.
  have hzero : eval ![(0 : ℂ), 1, 0] (pderiv 2 Fc) = 0 := by
    rw [hFGH, pderiv_mul]
    simp [hGP, hHP]
  have hone : eval ![(0 : ℂ), 1, 0] (pderiv 2 Fc) = 1 := by
    simp [Fc, pderiv_X]
  rw [hone] at hzero
  exact one_ne_zero hzero

/-! ## Finiteness, conditional on the two invoked general theorems -/

/-- **The two general theorems invoked by the paper**, packaged as a single hypothesis:
*a plane quartic over `ℚ` whose projective zero locus is smooth (Jacobian criterion over `ℂ`)
has only finitely many rational points.*

This is a true theorem, but not a formalizable-from-Mathlib one: a smooth plane curve is
geometrically irreducible, the genus formula gives it genus `(4-1)(4-2)/2 = 3 ≥ 2`, and
Faltings' theorem then says that its set of rational points is finite. Neither the genus
formula for plane curves nor Faltings' theorem is available in Mathlib, so — exactly as in the
paper, where both are invoked rather than proved — the statement is taken as a hypothesis. -/
def FaltingsSmoothPlaneQuartic : Prop :=
  ∀ G : MvPolynomial (Fin 3) ℚ, G.IsHomogeneous 4 →
    (∀ v : Fin 3 → ℂ, (∀ i, aeval v (pderiv i G) = 0) → v = 0) →
    {p : ℚ × ℚ | eval ![p.1, p.2, 1] G = 0}.Finite

/-- **Theorem 1 of the paper.** The equation `x⁴ + x y + y³ = 1` has only finitely many
rational solutions. -/
theorem rational_solutions_finite (faltings : FaltingsSmoothPlaneQuartic) :
    {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1}.Finite := by
  have h := faltings Fq Fq_isHomogeneous smooth
  have hset : {p : ℚ × ℚ | eval ![p.1, p.2, 1] Fq = 0}
      = {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1} := by
    ext p
    simp only [Set.mem_ofPred_eq, eval_affine]
    constructor <;> intro h' <;> linarith
  rwa [hset] at h

/-- **Corollary.** The equation `x⁴ + x y + y³ = 1` has only finitely many integer solutions. -/
theorem integer_solutions_finite (faltings : FaltingsSmoothPlaneQuartic) :
    {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1}.Finite := by
  have hQ := rational_solutions_finite faltings
  have hpre : {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1}
      = (fun p : ℤ × ℤ => ((p.1 : ℚ), (p.2 : ℚ))) ⁻¹'
        {p : ℚ × ℚ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro h; exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
    · intro h; exact_mod_cast h
  rw [hpre]
  refine Set.Finite.preimage ?_ hQ
  intro a _ b _ hab
  have h1 : (a.1 : ℚ) = (b.1 : ℚ) := congrArg Prod.fst hab
  have h2 : (a.2 : ℚ) = (b.2 : ℚ) := congrArg Prod.snd hab
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- **The infinitude claim refuted.** The set of integer solutions of `x⁴ + x y + y³ = 1` is
not infinite. -/
theorem not_infinite_integer_solutions (faltings : FaltingsSmoothPlaneQuartic) :
    ¬ {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1}.Infinite :=
  Set.not_infinite.2 (integer_solutions_finite faltings)

/-! ## The explicit small solutions (§4 of the paper) -/

/-- The five integer solutions listed in the paper are indeed solutions. -/
theorem five_solutions :
    ((-1 : ℤ) ^ 4 + (-1 : ℤ) * (-1 : ℤ) + (-1 : ℤ) ^ 3 = 1) ∧
    ((-1 : ℤ) ^ 4 + (-1 : ℤ) * (0 : ℤ) + (0 : ℤ) ^ 3 = 1) ∧
    ((-1 : ℤ) ^ 4 + (-1 : ℤ) * (1 : ℤ) + (1 : ℤ) ^ 3 = 1) ∧
    ((0 : ℤ) ^ 4 + (0 : ℤ) * (1 : ℤ) + (1 : ℤ) ^ 3 = 1) ∧
    ((1 : ℤ) ^ 4 + (1 : ℤ) * (0 : ℤ) + (0 : ℤ) ^ 3 = 1) := by
  norm_num

/-- **§4 of the paper.** The integer solutions with `|x| ≤ 1` are exactly the five listed
pairs. (This is unconditional; it does not show that there are no others with `|x| ≥ 2`.) -/
theorem solutions_with_small_x :
    {p : ℤ × ℤ | p.1 ^ 4 + p.1 * p.2 + p.2 ^ 3 = 1 ∧ |p.1| ≤ 1}
      = {(-1, -1), (-1, 0), (-1, 1), (0, 1), (1, 0)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨heq, habs⟩
    rw [abs_le] at habs
    obtain ⟨hl, hr⟩ := habs
    interval_cases x
    · -- x = -1 : y³ = y
      have h : y * (y - 1) * (y + 1) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact Or.inr (Or.inl ⟨rfl, h''⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩))
      · exact Or.inl ⟨rfl, by linarith⟩
    · -- x = 0 : y³ = 1
      have h : (y - 1) * (y ^ 2 + y + 1) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩)))
      · nlinarith [sq_nonneg (2 * y + 1)]
    · -- x = 1 : y³ + y = 0
      have h : y * (y ^ 2 + 1) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h'⟩)))
      · nlinarith [sq_nonneg y]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end QuarticCurve
