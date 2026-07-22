import Mathlib
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace PolynomialParametrization
/-- The affine surface from the paper: `x³ + yz + 1 = 0`. -/
def OnSurface {R : Type*} [CommRing R] (p : R × R × R) : Prop :=
  p.1 ^ 3 + p.2.1 * p.2.2 + 1 = 0
/-- The paper's two-parameter polynomial map. -/
def param {R : Type*} [CommRing R] (a b : R) : R × R × R :=
  (a * b - 1, a, -b * (a ^ 2 * b ^ 2 - 3 * a * b + 3))
/-- The polynomial map always lands on the surface (Theorem 1). -/
theorem param_onSurface {R : Type*} [CommRing R] (a b : R) :
    OnSurface (param a b) := by
  simp [OnSurface, param]
  ring
/-- The one-parameter family in Corollary 2. -/
def firstFamily {R : Type*} [CommRing R] (t : R) : R × R × R :=
  (t, t + 1, -(t ^ 2 - t + 1))
theorem firstFamily_eq_param {R : Type*} [CommRing R] (t : R) :
    firstFamily t = param (t + 1) 1 := by
  simp [firstFamily, param]
  ring
theorem firstFamily_onSurface {R : Type*} [CommRing R] (t : R) :
    OnSurface (firstFamily t) := by
  rw [firstFamily_eq_param]
  exact param_onSurface _ _
theorem firstFamily_injective : Function.Injective (firstFamily (R := ℤ)) := by
  intro s t h
  exact congrArg Prod.fst h
/-- Thus the integral surface has infinitely many points. -/
theorem integral_surface_infinite : Set.Infinite {p : ℤ × ℤ × ℤ | OnSurface p} := by
  apply Set.infinite_of_injective_forall_mem firstFamily_injective
  exact firstFamily_onSurface
/-- The explicit inverse to the rational parametrization from equation (4). -/
def rationalInverse (p : ℚ × ℚ × ℚ) : ℚ × ℚ :=
  if p.2.1 = 0 then (0, -p.2.2 / 3) else (p.2.1, (p.1 + 1) / p.2.1)
theorem rationalInverse_param (a b : ℚ) :
    rationalInverse (param a b) = (a, b) := by
  unfold rationalInverse param
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]
theorem param_rationalInverse (p : ℚ × ℚ × ℚ) (hp : OnSurface p) :
    param (rationalInverse p).1 (rationalInverse p).2 = p := by
  unfold rationalInverse
  by_cases hy : p.2.1 = 0
  · -- Case y = 0: from surface equation, x³ + 1 = 0, so x = -1
    simp [hy]
    simp [OnSurface] at hp
    rw [hy] at hp
    have hx : p.1 = -1 := by nlinarith [sq_nonneg (p.1), sq_nonneg (p.1 + 1), sq_nonneg (p.1 - 1)]
    simp [param]
    exact Prod.ext hx.symm (Prod.ext hy.symm rfl)
  · -- Case y ≠ 0: rationalInverse = (y, (x+1)/y)
    simp [hy]
    simp [OnSurface] at hp
    have hkey : p.2.1 * p.2.2 = -(p.1 + 1) * (p.1 ^ 2 - p.1 + 1) := by nlinarith
    simp [param]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · field_simp
      ring
    · rfl
    · field_simp
      ring_nf
      linarith [hkey]
/-- Theorem 3: over `ℚ`, the polynomial map is a bijection onto all rational points. -/
theorem rational_bijection :
    Function.Bijective
      (fun q : ℚ × ℚ => (⟨param q.1 q.2, param_onSurface q.1 q.2⟩ :
        {p : ℚ × ℚ × ℚ // OnSurface p})) := by
  constructor
  · intro q r h
    have hv : param q.1 q.2 = param r.1 r.2 := congrArg Subtype.val h
    have hi := congrArg rationalInverse hv
    simpa only [rationalInverse_param] using hi
  · intro p
    refine ⟨rationalInverse p.1, ?_⟩
    apply Subtype.ext
    exact param_rationalInverse p.1 p.2
/-- Proposition 4: exact characterization of integral points obtained from integral parameters. -/
theorem integral_mem_param_iff (p : ℤ × ℤ × ℤ) (hp : OnSurface p) :
    (∃ a b : ℤ, param a b = p) ↔
      (p.2.1 ≠ 0 ∧ p.2.1 ∣ p.1 + 1) ∨ (p.2.1 = 0 ∧ (3 : ℤ) ∣ p.2.2) := by
  constructor
  · intro ⟨a, b, hab⟩
    simp [param] at hab
    by_cases ha : a = 0
    · right
      simp [ha] at hab
      rw [← hab]
      simp
    · left
      rw [← hab]
      simp [ha]
  · intro h
    rcases h with ⟨hy, hdvd⟩ | ⟨hy, hdiv⟩
    · -- Case: y ≠ 0 and y ∣ x + 1
      use p.2.1, (p.1 + 1) / p.2.1
      simp [param]
      have hab : p.2.1 * ((p.1 + 1) / p.2.1) = p.1 + 1 := Int.mul_ediv_cancel' hdvd
      -- First component: p.2.1 * ((p.1 + 1) / p.2.1) - 1 = p.1
      -- Second component: p.2.1 = p.2.1
      -- Third component: need to show using surface equation
      have h1 : p.2.1 * ((p.1 + 1) / p.2.1) - 1 = p.1 := by rw [hab]; ring
      rw [h1]
      -- Need to show third component equals p.2.2
      -- From surface: p.1^3 + p.2.1 * p.2.2 + 1 = 0
      simp [OnSurface] at hp
      ext <;> try rfl
      -- Need: -(b * (y^2 * b^2 - 3*y*b + 3)) = p.2.2
      -- where b = (p.1+1)/y, y = p.2.1
      -- Using y*b = p.1+1, this simplifies to -b*(p.1^2 - p.1 + 1) = p.2.2
      -- From hp: p.2.2 = -(p.1^3 + 1)/p.2.1 = -(p.1+1)*(p.1^2 - p.1 + 1)/p.2.1 = -b*(p.1^2 - p.1 + 1)
      set y := p.2.1 with hy'
      set b := (p.1 + 1) / p.2.1 with hb'
      have hyb : y * b = p.1 + 1 := hab
      have h2 : y ^ 2 * b ^ 2 = (p.1 + 1) ^ 2 := by rw [← hyb]; ring
      have h3 : 3 * y * b = 3 * (p.1 + 1) := by rw [← hyb]; ring
      rw [h2, h3]
      -- (p.1 + 1)^2 - 3*(p.1 + 1) + 3 = p.1^2 - p.1 + 1
      have h4 : (p.1 + 1) ^ 2 - 3 * (p.1 + 1) + 3 = p.1 ^ 2 - p.1 + 1 := by ring
      rw [h4]
      -- From hp: y * p.2.2 = -(p.1^3 + 1) = -(p.1+1)(p.1^2 - p.1 + 1) = -y*b*(p.1^2 - p.1 + 1)
      -- Since y ≠ 0, p.2.2 = -b*(p.1^2 - p.1 + 1)
      have key : y * p.2.2 = -(p.1 + 1) * (p.1 ^ 2 - p.1 + 1) := by linarith [hp, (by ring : p.1 ^ 3 + 1 = (p.1 + 1) * (p.1 ^ 2 - p.1 + 1)) ]
      rw [← hyb] at key
      -- key: y * p.2.2 = -(y * b) * (p.1^2 - p.1 + 1) = -y * b * (p.1^2 - p.1 + 1)
      have key' : y * p.2.2 = y * (-(b * (p.1 ^ 2 - p.1 + 1))) := by linarith
      have key'' : p.2.2 = - (b * (p.1 ^ 2 - p.1 + 1)) := mul_left_cancel₀ hy key'
      linarith
    · -- Case: y = 0 and 3 ∣ z
      -- From OnSurface: p.1^3 + 1 = 0, so p.1 = -1
      have hx : p.1 = -1 := by
        simp [OnSurface] at hp
        rw [hy] at hp
        have : p.1 ^ 3 = -1 := by linarith
        nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
      use 0, -p.2.2 / 3
      have hp_eq : p = (-1, 0, p.2.2) := by ext <;> simp [hx, hy]
      simp [param]
      rw [hp_eq]
      simp
      have : (-p.2.2) / 3 * 3 = -p.2.2 := Int.ediv_mul_cancel (dvd_neg.mpr hdiv)
      linarith
/-- In the nonzero-`y` case, the integral parameters are uniquely those in Proposition 4. -/
theorem integral_params_unique_of_y_ne_zero
    (p : ℤ × ℤ × ℤ) (_hp : OnSurface p) (hy : p.2.1 ≠ 0)
    (a b : ℤ) (hab : param a b = p) :
    a = p.2.1 ∧ b = (p.1 + 1) / p.2.1 := by
  have ha : a = p.2.1 := congrArg (fun q => q.2.1) hab
  have hx : a * b - 1 = p.1 := congrArg Prod.fst hab
  constructor
  · exact ha
  · rw [← ha, ← hx]
    exact (Int.ediv_eq_of_eq_mul_left (ha ▸ hy) (by ring)).symm
/-- In the zero-`y` case, the integral parameters are uniquely those in Proposition 4. -/
theorem integral_params_unique_of_y_eq_zero
    (p : ℤ × ℤ × ℤ) (_hp : OnSurface p) (hy : p.2.1 = 0)
    (a b : ℤ) (hab : param a b = p) :
    a = 0 ∧ b = -p.2.2 / 3 := by
  have ha' : a = p.2.1 := congrArg (fun q => q.2.1) hab
  have ha : a = 0 := ha'.trans hy
  have hz := congrArg (fun q => q.2.2) hab
  subst a
  constructor
  · exact hy
  · rw [hy] at hz
    simp [param] at hz
    rw [← hz]
    omega
/-- The integral solution `(2,9,-1)` from Remark 5. -/
theorem exceptional_point_onSurface : OnSurface ((2, 9, -1) : ℤ × ℤ × ℤ) := by
  simp [OnSurface]
/-- Remark 5: `(2,9,-1)` is not obtained from integral parameter values. -/
theorem exceptional_point_not_integrally_parametrized :
    ¬ ∃ a b : ℤ, param a b = ((2, 9, -1) : ℤ × ℤ × ℤ) := by
  intro ⟨a, b, h⟩
  simp [param] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h2] at h1
  omega
/-- The second one-parameter family in Proposition 6. -/
def secondFamily {R : Type*} [CommRing R] (t : R) : R × R × R :=
  (-t ^ 2, t ^ 3 - 1, t ^ 3 + 1)
theorem secondFamily_onSurface {R : Type*} [CommRing R] (t : R) :
    OnSurface (secondFamily t) := by
  simp [OnSurface, secondFamily]
  ring
end PolynomialParametrization
