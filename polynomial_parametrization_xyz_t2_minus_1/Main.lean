import Mathlib
set_option autoImplicit false
namespace PolynomialParametrization
/-- A point `(x,y,z,t)` on the affine hypersurface `xyz + t² - 1 = 0`. -/
@[ext]
structure Point (R : Type*) where
  x : R
  y : R
  z : R
  t : R
  deriving DecidableEq
/-- The equation studied in the paper. -/
def OnSurface {R : Type*} [Ring R] (p : Point R) : Prop :=
  p.x * p.y * p.z + p.t ^ 2 - 1 = 0
/-- The polynomial chart `Φ_ε(a,b,c)`. -/
def phi {R : Type*} [Ring R] (ε a b c : R) : Point R :=
  ⟨a, b, c * (2 - a * b * c), ε * (1 - a * b * c)⟩
/-- The parametrization is a polynomial identity over every commutative ring. -/
theorem phi_onSurface {R : Type*} [CommRing R] {ε : R} (hε : ε ^ 2 = 1)
    (a b c : R) : OnSurface (phi ε a b c) := by
  simp [OnSurface, phi]
  rw [show (ε * (1 - a * b * c)) ^ 2 = ε ^ 2 * (1 - a * b * c) ^ 2 by ring, hε]
  ring
/-- On `xy ≠ 0`, the first chart has the inverse stated in the paper. -/
theorem phi_one_inverse (p : Point ℚ) (hp : OnSurface p) (hxy : p.x * p.y ≠ 0) :
    phi 1 p.x p.y ((1 - p.t) / (p.x * p.y)) = p := by
  have hq : p.x * p.y * ((1 - p.t) / (p.x * p.y)) = 1 - p.t := by
    exact mul_div_cancel₀ _ hxy
  have hprod : (1 - p.t) * (1 + p.t) = (p.x * p.y) * p.z := by
    dsimp [OnSurface] at hp
    nlinarith
  have hc : (1 - p.t) / (p.x * p.y) *
      (2 - p.x * p.y * ((1 - p.t) / (p.x * p.y))) = p.z := by
    rw [hq]
    rw [show 2 - (1 - p.t) = 1 + p.t by ring]
    rw [div_mul_eq_mul_div, hprod]
    exact mul_div_cancel_left₀ p.z hxy
  apply Point.ext <;> simp [phi]
  · simpa only [hq] using hc
  · linarith [hq]
/-- The two signs are jointly exhaustive over the rationals. -/
theorem rational_exhaustive (p : Point ℚ) (hp : OnSurface p) :
    (∃ a b c : ℚ, p = phi 1 a b c) ∨ (∃ a b c : ℚ, p = phi (-1) a b c) := by
  by_cases hxy : p.x * p.y = 0
  · have ht : p.t = 1 ∨ p.t = -1 := by
      dsimp [OnSurface] at hp
      have : p.x * p.y * p.z = 0 := by rw [hxy]; ring
      rw [this] at hp
      exact sq_eq_one_iff.mp (by nlinarith)
    rcases ht with ht | ht
    · left
      refine ⟨p.x, p.y, p.z / 2, ?_⟩
      apply Point.ext <;> simp [phi, hxy, ht]
    · right
      refine ⟨p.x, p.y, p.z / 2, ?_⟩
      apply Point.ext <;> simp [phi, hxy, ht]
  · left
    exact ⟨p.x, p.y, (1 - p.t) / (p.x * p.y),
      (phi_one_inverse p hp hxy).symm⟩
/-- Conversely, applying the displayed inverse to a point in the first chart recovers `c`
when `ab ≠ 0`; this records the claimed open-set isomorphism. -/
theorem inverse_phi_one (a b c : ℚ) (hab : a * b ≠ 0) :
    (1 - (phi 1 a b c).t) / ((phi 1 a b c).x * (phi 1 a b c).y) = c := by
  simp only [phi, one_mul]
  apply (div_eq_iff hab).2
  ring
/-- Every choice of three integer parameters and either sign gives an integer solution. -/
theorem integer_family (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (a b c : ℤ) :
    OnSurface (phi ε a b c) := by
  apply phi_onSurface
  rcases hε with rfl | rfl <;> norm_num
/-- The one-parameter subfamily used in the paper consists of pairwise distinct points. -/
theorem integer_family_injective : Function.Injective
    (fun n : ℤ => phi 1 (1 : ℤ) (1 : ℤ) n) := by
  intro m n h
  have ht := congrArg Point.t h
  simpa [phi] using ht
/-- Exact integrality criterion for the `Φ₁` chart on the nondegenerate locus. -/
theorem integral_preimage_one_iff (p : Point ℤ) (hp : OnSurface p)
    (hxy : p.x * p.y ≠ 0) :
    (∃ a b c : ℤ, p = phi 1 a b c) ↔ p.x * p.y ∣ 1 - p.t := by
  constructor
  · intro ⟨a, b, c, hp'⟩
    rw [hp']
    simp [phi]
  · intro hdiv
    obtain ⟨c, hc⟩ := hdiv
    use p.x, p.y, c
    have hp' : p.x * p.y * p.z + p.t ^ 2 = 1 := by rw [OnSurface] at hp; rw [sub_eq_zero] at hp; exact hp
    have hsurf : p.x * p.y * p.z = 1 - p.t ^ 2 := by linarith
    have ht : p.t = 1 - p.x * p.y * c := by linarith
    have hz : p.z = c * (2 - p.x * p.y * c) := by
      have h1 : c * (1 + p.t) = p.z := by
        have h2 : (1 - p.t) * (1 + p.t) = p.x * p.y * p.z := by linarith
        rw [hc] at h2
        have h3 : p.x * p.y * (c * (1 + p.t)) = p.x * p.y * p.z := by ring_nf at h2; linarith
        exact (mul_left_cancel₀ hxy h3)
      have h1' : c * (2 - p.x * p.y * c) = p.z := by rw [ht] at h1; ring_nf at h1 ⊢; linarith
      linarith
    rw [phi]
    cases p
    simp_all
/-- When it exists, the integral preimage under `Φ₁` is unique. -/
theorem integral_preimage_one_unique (p : Point ℤ)
    (hxy : p.x * p.y ≠ 0) (a b c : ℤ) (h : p = phi 1 a b c) :
    a = p.x ∧ b = p.y ∧ c = (1 - p.t) / (p.x * p.y) := by
  have hx : a = p.x := by simpa [phi] using congrArg Point.x h.symm
  have hy : b = p.y := by simpa [phi] using congrArg Point.y h.symm
  refine ⟨hx, hy, ?_⟩
  have ht : 1 - p.t = (p.x * p.y) * c := by
    have := congrArg Point.t h
    simp [phi] at this
    rw [← hx, ← hy]
    linarith
  exact (Int.ediv_eq_of_eq_mul_left hxy (by simpa [mul_comm] using ht)).symm
/-- Exact integrality criterion for the `Φ₋₁` chart on the nondegenerate locus. -/
theorem integral_preimage_neg_one_iff (p : Point ℤ) (hp : OnSurface p)
    (hxy : p.x * p.y ≠ 0) :
    (∃ a b c : ℤ, p = phi (-1) a b c) ↔ p.x * p.y ∣ 1 + p.t := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    simp [phi]
  · intro hdiv
    obtain ⟨c, hc⟩ := hdiv
    use p.x, p.y, c
    simp [phi]
    have ht : p.t = p.x * p.y * c - 1 := by linarith
    have hpz : p.z = c * (2 - p.x * p.y * c) := by
      have hsurf := hp
      simp [OnSurface] at hsurf
      rw [ht] at hsurf
      have h1 : p.x * p.y * (p.z + p.x * p.y * c ^ 2 - 2 * c) = 0 := by linarith
      have h2 : p.z + p.x * p.y * c ^ 2 - 2 * c = 0 := (mul_eq_zero.mp h1).resolve_left hxy
      linarith
    have : p = ⟨p.x, p.y, p.z, p.t⟩ := rfl
    rw [this, hpz, ht]
/-- When it exists, the integral preimage under `Φ₋₁` is unique. -/
theorem integral_preimage_neg_one_unique (p : Point ℤ)
    (hxy : p.x * p.y ≠ 0) (a b c : ℤ) (h : p = phi (-1) a b c) :
    a = p.x ∧ b = p.y ∧ c = (1 + p.t) / (p.x * p.y) := by
  have hx : a = p.x := by simpa [phi] using congrArg Point.x h.symm
  have hy : b = p.y := by simpa [phi] using congrArg Point.y h.symm
  refine ⟨hx, hy, ?_⟩
  have ht : 1 + p.t = (p.x * p.y) * c := by
    have := congrArg Point.t h
    simp [phi] at this
    rw [← hx, ← hy]
    linarith
  exact (Int.ediv_eq_of_eq_mul_left hxy (by simpa [mul_comm] using ht)).symm
/-- The paper's example really lies on the integer surface. -/
theorem exceptional_point_onSurface :
    OnSurface (Point.mk (30 : ℤ) 42 (-4) 71) := by
  norm_num [OnSurface]
/-- None of the three pairwise products in the example divides either `1-t` or `1+t`. -/
theorem exceptional_point_divisibility :
    let p : Point ℤ := ⟨30, 42, -4, 71⟩
    ¬ p.x * p.y ∣ 1 - p.t ∧ ¬ p.x * p.y ∣ 1 + p.t ∧
    ¬ p.x * p.z ∣ 1 - p.t ∧ ¬ p.x * p.z ∣ 1 + p.t ∧
    ¬ p.y * p.z ∣ 1 - p.t ∧ ¬ p.y * p.z ∣ 1 + p.t := by
  norm_num
end PolynomialParametrization
