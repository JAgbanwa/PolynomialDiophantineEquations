import Mathlib
import RequestProject.FunctionField
/-!
# Powerful values of polynomials over function fields
This file complements `RequestProject.FunctionField`.  There the equation
`a x^p y^q = b z^r + c` was treated; here the right-hand side is allowed to be an
*arbitrary* squarefree cubic in `z`, which covers the two remaining equations of Table 12 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*, of the shape
"powerful value of a cubic":
* `x³ y² = z³ − z + 1` and `x³ y² = z³ + z + 1`   (Problem 4 open).
The mechanism is again Mason–Stothers.  If `x^p y^q` (with `p, q ≥ 2`) equals
`c (z − ρ₁)(z − ρ₂)(z − ρ₃)` with `ρ₁, ρ₂, ρ₃` distinct, then
* the three factors `z − ρᵢ` are pairwise coprime, so the degrees of their radicals add up to
  at most `deg rad (x^p y^q) ≤ deg x + deg y ≤ ½ deg (x^p y^q) = (3/2) deg z`;
* Mason–Stothers applied to `(z − ρᵢ) − (z − ρⱼ) = ρⱼ − ρᵢ` gives
  `deg z + 1 ≤ deg rad (z − ρᵢ) + deg rad (z − ρⱼ)` for each of the three pairs.
Adding the three pair inequalities gives `3 deg z + 3 ≤ 2 · (3/2) deg z = 3 deg z`, a
contradiction unless `z` is constant.
## Main results
* `FunctionField.natDegree_succ_le_radical_pair` — the Mason–Stothers estimate for a pair.
* `FunctionField.constant_of_powerful_eq_pow_add_const` — if a *powerful* polynomial `P`
  (one with `2 deg rad P ≤ deg P`) equals `b z^r + c` with `r ≥ 2` and `b, c ≠ 0`, then `z`
  and `P` are constant; this generalises the main theorem of `RequestProject.FunctionField`.
* `FunctionField.constant_of_pow_mul_pow_eq_split_cubic` — the theorem above.
* `FunctionField.constant_of_pow_mul_pow_eq_separable_cubic` — its form over an algebraically
  closed field, for an arbitrary monic separable cubic.
* `FunctionField.cubeSubXAddOne_constant`, `FunctionField.cubeAddXAddOne_constant` — the two
  equations `x³y² = z³ − z + 1` and `x³y² = z³ + z + 1` over `ℚ` have no nonconstant
  polynomial solutions.
-/
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain
namespace FunctionField
variable {k : Type*} [Field k] [CharZero k] [DecidableEq k]
/-- **Mason–Stothers for a pair of shifts.**  For `r ≠ s` and nonconstant `z`,
`deg z + 1 ≤ deg rad (z − r) + deg rad (z − s)`. -/
theorem natDegree_succ_le_radical_pair {z : k[X]} {r s : k} (hrs : r ≠ s)
    (hz : z.natDegree ≠ 0) :
    z.natDegree + 1 ≤ (radical (z - C r)).natDegree + (radical (z - C s)).natDegree := by
  set A : k[X] := z - C r with hA
  set B : k[X] := -(z - C s) with hB
  set D : k[X] := C (r - s) with hD
  have hdA : A.natDegree = z.natDegree := by rw [hA, natDegree_sub_C]
  have hdB : B.natDegree = z.natDegree := by rw [hB, natDegree_neg, natDegree_sub_C]
  have hA0 : A ≠ 0 := fun h0 => hz (by rw [← hdA, h0, natDegree_zero])
  have hB0 : B ≠ 0 := fun h0 => hz (by rw [← hdB, h0, natDegree_zero])
  have hrs' : r - s ≠ 0 := sub_ne_zero.2 hrs
  have hD0 : D ≠ 0 := by rw [hD, Ne, C_eq_zero]; exact hrs'
  have hsum : A + B + D = 0 := by rw [hA, hB, hD, map_sub]; ring
  have hcop : IsCoprime A B := by
    refine ⟨C (s - r)⁻¹, C (s - r)⁻¹, ?_⟩
    have hAB : A + B = C (s - r) := by rw [hA, hB, map_sub]; ring
    calc C (s - r)⁻¹ * A + C (s - r)⁻¹ * B = C (s - r)⁻¹ * (A + B) := by ring
      _ = C (s - r)⁻¹ * C (s - r) := by rw [hAB]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.2 hrs.symm), map_one]
  rcases Polynomial.abc hA0 hB0 hD0 hcop hsum with ⟨h1, _, _⟩ | ⟨d1, _, _⟩
  · have hrad : radical (A * B * D) ∣ radical A * radical B := by
      refine dvd_trans radical_mul_dvd ?_
      have hDr : radical D = 1 := by
        rw [hD]; exact radical_of_isUnit (isUnit_C.2 hrs'.isUnit)
      rw [hDr, mul_one]
      exact radical_mul_dvd
    have hle : (radical (A * B * D)).natDegree ≤ (radical A).natDegree + (radical B).natDegree := by
      refine le_trans (natDegree_le_of_dvd hrad (mul_ne_zero radical_ne_zero radical_ne_zero)) ?_
      rw [natDegree_mul radical_ne_zero radical_ne_zero]
    have hrB : radical B = radical (z - C s) := by rw [hB, radical_neg]
    rw [hdA] at h1
    rw [hrB] at hle
    omega
  · have hd0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero d1
    rw [hdA] at hd0
    exact absurd hd0 hz
omit [CharZero k] in
/-- A product `x^p y^q` with `p, q ≥ 2` is *powerful*: twice the degree of its radical is at
most its degree. -/
theorem two_mul_natDegree_radical_le {x y : k[X]} (hx : x ≠ 0) (hy : y ≠ 0) {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) :
    2 * (radical (x ^ p * y ^ q)).natDegree ≤ (x ^ p * y ^ q).natDegree := by
  have hdvd : radical (x ^ p * y ^ q) ∣ radical x * radical y := by
    refine dvd_trans radical_mul_dvd ?_
    rw [radical_pow _ (by omega : p ≠ 0), radical_pow _ (by omega : q ≠ 0)]
  have h1 : (radical (x ^ p * y ^ q)).natDegree ≤ x.natDegree + y.natDegree := by
    refine le_trans (natDegree_le_of_dvd hdvd (mul_ne_zero radical_ne_zero radical_ne_zero)) ?_
    rw [natDegree_mul radical_ne_zero radical_ne_zero]
    exact Nat.add_le_add natDegree_radical_le natDegree_radical_le
  have h2 : (x ^ p * y ^ q).natDegree = p * x.natDegree + q * y.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ hx) (pow_ne_zero _ hy), natDegree_pow, natDegree_pow]
  have e1 : 2 * x.natDegree ≤ p * x.natDegree := Nat.mul_le_mul_right _ hp
  have e2 : 2 * y.natDegree ≤ q * y.natDegree := Nat.mul_le_mul_right _ hq
  omega
/-- **Powerful values of `b z^r + c`.**  If `P` is powerful (`2 deg rad P ≤ deg P`) and
`P = b z^r + c` with `r ≥ 2` and `b, c ≠ 0` constants, then `z` and `P` are constant.
This generalises `FunctionField.constant_of_pow_mul_pow_eq`, whose left-hand side
`a x^p y^q` with `p, q ≥ 2` is a particular powerful polynomial
(see `two_mul_natDegree_radical_le`). -/
theorem constant_of_powerful_eq_pow_add_const {P z : k[X]} {b c : k} (r : ℕ) (hr : 2 ≤ r)
    (hb : b ≠ 0) (hc : c ≠ 0) (hpow : 2 * (radical P).natDegree ≤ P.natDegree)
    (h : P = C b * z ^ r + C c) :
    z.natDegree = 0 ∧ P.natDegree = 0 := by
  have hCb : (C b : k[X]) ≠ 0 := by simpa using hb
  have hnb : (-b) ≠ 0 := neg_ne_zero.2 hb
  have hCnb : (C (-b) : k[X]) ≠ 0 := by simpa using hnb
  have hz : z.natDegree = 0 := by
    by_contra hz0
    have hz' : z ≠ 0 := fun h0 => hz0 (by rw [h0, natDegree_zero])
    set B : k[X] := C (-b) * z ^ r with hB
    set D : k[X] := C (-c) with hD
    have hB0 : B ≠ 0 := mul_ne_zero hCnb (pow_ne_zero _ hz')
    have hD0 : D ≠ 0 := by rw [hD, Ne, C_eq_zero]; exact neg_ne_zero.2 hc
    have hsum : P + B + D = 0 := by rw [h, hB, hD, map_neg, map_neg]; ring
    have hdegB : B.natDegree = r * z.natDegree := by
      rw [hB, natDegree_mul hCnb (pow_ne_zero _ hz'), natDegree_C, natDegree_pow, zero_add]
    have hdegbz : (C b * z ^ r).natDegree = r * z.natDegree := by
      rw [natDegree_mul hCb (pow_ne_zero _ hz'), natDegree_C, natDegree_pow, zero_add]
    have hdegA : P.natDegree = r * z.natDegree := by rw [h, natDegree_add_C, hdegbz]
    have hA0 : P ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hdegA
      rcases Nat.mul_eq_zero.1 hdegA.symm with h' | h' <;> omega
    have hcop : IsCoprime P B := by
      refine ⟨C c⁻¹, C c⁻¹, ?_⟩
      have hAB : P + B = C c := by
        have hDc : D = -C c := by rw [hD, map_neg]
        linear_combination hsum - hDc
      calc C c⁻¹ * P + C c⁻¹ * B = C c⁻¹ * (P + B) := by ring
        _ = C c⁻¹ * C c := by rw [hAB]
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rcases Polynomial.abc hA0 hB0 hD0 hcop hsum with ⟨h1, _, _⟩ | ⟨d1, _, _⟩
    · have hrad : radical (P * B * D) ∣ radical P * radical z := by
        refine dvd_trans radical_mul_dvd ?_
        have hDr : radical D = 1 := by
          rw [hD]; exact radical_of_isUnit (isUnit_C.2 (neg_ne_zero.2 hc).isUnit)
        rw [hDr, mul_one]
        refine dvd_trans radical_mul_dvd ?_
        have hBr : radical B = radical z := by
          rw [hB, radical_mul_of_isUnit_left (isUnit_C.2 hnb.isUnit), radical_pow _ (by omega)]
        rw [hBr]
      have hle : (radical (P * B * D)).natDegree ≤ (radical P).natDegree + z.natDegree := by
        refine le_trans (natDegree_le_of_dvd hrad (mul_ne_zero radical_ne_zero radical_ne_zero)) ?_
        rw [natDegree_mul radical_ne_zero radical_ne_zero]
        exact Nat.add_le_add_left natDegree_radical_le _
      rw [hdegA] at h1
      have e3 : 2 * z.natDegree ≤ r * z.natDegree := Nat.mul_le_mul_right _ hr
      omega
    · have hd0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero d1
      rw [hdegA] at hd0
      rcases Nat.mul_eq_zero.1 hd0 with h' | h' <;> omega
  refine ⟨hz, ?_⟩
  have h1 : (C b * z ^ r).natDegree = 0 :=
    Nat.le_zero.1 (le_trans natDegree_mul_le (by simp [natDegree_pow, hz]))
  rw [h]
  exact Nat.le_zero.1 (le_trans (natDegree_add_le _ _) (by simp [h1]))
/-- The key estimate: a polynomial `P` whose radical has degree at most `½ deg P` cannot equal
`c (z − ρ₁)(z − ρ₂)(z − ρ₃)` with `ρ₁, ρ₂, ρ₃` distinct, unless `z` is constant. -/
theorem constant_of_powerful_of_three_distinct_roots {P z : k[X]} {c r₁ r₂ r₃ : k} (hc : c ≠ 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (hpow : 2 * (radical P).natDegree ≤ P.natDegree)
    (h : P = C c * ((z - C r₁) * (z - C r₂) * (z - C r₃))) :
    z.natDegree = 0 := by
  by_contra hz
  have b₁₂ := natDegree_succ_le_radical_pair (z := z) h₁₂ hz
  have b₁₃ := natDegree_succ_le_radical_pair (z := z) h₁₃ hz
  have b₂₃ := natDegree_succ_le_radical_pair (z := z) h₂₃ hz
  set A₁ : k[X] := z - C r₁ with hA₁
  set A₂ : k[X] := z - C r₂ with hA₂
  set A₃ : k[X] := z - C r₃ with hA₃
  have hd : ∀ r : k, (z - C r).natDegree = z.natDegree := fun _ => natDegree_sub_C
  have hne : ∀ r : k, (z - C r) ≠ 0 := fun r h0 => hz (by rw [← hd r, h0, natDegree_zero])
  have hCc : (C c : k[X]) ≠ 0 := by simpa using hc
  have hP0 : P ≠ 0 := by
    rw [h]
    exact mul_ne_zero hCc (mul_ne_zero (mul_ne_zero (hne _) (hne _)) (hne _))
  have hdegP : P.natDegree = 3 * z.natDegree := by
    rw [h, natDegree_mul hCc (mul_ne_zero (mul_ne_zero (hne _) (hne _)) (hne _)),
      natDegree_mul (mul_ne_zero (hne _) (hne _)) (hne _),
      natDegree_mul (hne _) (hne _), natDegree_C, hd, hd, hd]
    ring
  have hcopAux : ∀ r s : k, r ≠ s → IsCoprime (z - C r) (z - C s) := by
    intro r s hrs
    refine ⟨C (s - r)⁻¹, -C (s - r)⁻¹, ?_⟩
    have hAB : (z - C r) - (z - C s) = C (s - r) := by rw [map_sub]; ring
    calc C (s - r)⁻¹ * (z - C r) + -C (s - r)⁻¹ * (z - C s)
        = C (s - r)⁻¹ * ((z - C r) - (z - C s)) := by ring
      _ = C (s - r)⁻¹ * C (s - r) := by rw [hAB]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.2 hrs.symm), map_one]
  have hd₁ : A₁ ∣ P := by rw [h]; exact ⟨C c * (A₂ * A₃), by ring⟩
  have hd₂ : A₂ ∣ P := by rw [h]; exact ⟨C c * (A₁ * A₃), by ring⟩
  have hd₃ : A₃ ∣ P := by rw [h]; exact ⟨C c * (A₁ * A₂), by ring⟩
  have hcop₁₂ : IsCoprime (radical A₁) (radical A₂) :=
    ((hcopAux _ _ h₁₂).of_isCoprime_of_dvd_left radical_dvd_self).of_isCoprime_of_dvd_right
      radical_dvd_self
  have hcop₁₃ : IsCoprime (radical A₁) (radical A₃) :=
    ((hcopAux _ _ h₁₃).of_isCoprime_of_dvd_left radical_dvd_self).of_isCoprime_of_dvd_right
      radical_dvd_self
  have hcop₂₃ : IsCoprime (radical A₂) (radical A₃) :=
    ((hcopAux _ _ h₂₃).of_isCoprime_of_dvd_left radical_dvd_self).of_isCoprime_of_dvd_right
      radical_dvd_self
  have hprod : radical A₁ * radical A₂ * radical A₃ ∣ radical P :=
    (hcop₁₃.mul_left hcop₂₃).mul_dvd
      (hcop₁₂.mul_dvd (radical_dvd_radical hd₁ hP0) (radical_dvd_radical hd₂ hP0))
      (radical_dvd_radical hd₃ hP0)
  have hsum : (radical A₁).natDegree + (radical A₂).natDegree + (radical A₃).natDegree
      ≤ (radical P).natDegree := by
    refine le_trans (le_of_eq ?_) (natDegree_le_of_dvd hprod radical_ne_zero)
    rw [natDegree_mul (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero,
      natDegree_mul radical_ne_zero radical_ne_zero]
  omega
/-- If `x^p y^q` (with `p, q ≥ 2`) is a constant multiple of a product of three distinct linear
factors of `z`, then `x`, `y` and `z` are all constant. -/
theorem constant_of_pow_mul_pow_eq_split_cubic {x y z : k[X]} {c r₁ r₂ r₃ : k} {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (h : x ^ p * y ^ q = C c * ((z - C r₁) * (z - C r₂) * (z - C r₃))) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  have hzd : z.natDegree = 0 :=
    constant_of_powerful_of_three_distinct_roots hc h₁₂ h₁₃ h₂₃
      (two_mul_natDegree_radical_le hx hy hp hq) h
  have h1 : ∀ r : k, (z - C r).natDegree = 0 := fun r => by rw [natDegree_sub_C, hzd]
  have t1 : ((z - C r₁) * (z - C r₂)).natDegree = 0 :=
    Nat.le_zero.1 (le_trans natDegree_mul_le (by simp [h1]))
  have t2 : ((z - C r₁) * (z - C r₂) * (z - C r₃)).natDegree = 0 :=
    Nat.le_zero.1 (le_trans natDegree_mul_le (by simp [t1, h1]))
  have hRHS : (C c * ((z - C r₁) * (z - C r₂) * (z - C r₃))).natDegree = 0 :=
    Nat.le_zero.1 (le_trans natDegree_mul_le (by simp [t2]))
  have hdeg : (x ^ p * y ^ q).natDegree = p * x.natDegree + q * y.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ hx) (pow_ne_zero _ hy), natDegree_pow, natDegree_pow]
  rw [h, hRHS] at hdeg
  have hx0 : x.natDegree = 0 := by
    rcases Nat.mul_eq_zero.1 (show p * x.natDegree = 0 by omega) with h' | h' <;> omega
  have hy0 : y.natDegree = 0 := by
    rcases Nat.mul_eq_zero.1 (show q * y.natDegree = 0 by omega) with h' | h' <;> omega
  exact ⟨hx0, hy0, hzd⟩
/-! ## Splitting a separable cubic over an algebraically closed field -/
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
omit [CharZero K] in
/-- A monic separable cubic over an algebraically closed field splits into three distinct
linear factors. -/
theorem exists_three_distinct_roots {h : K[X]} (hm : h.Monic) (hdeg : h.natDegree = 3)
    (hsep : h.Separable) :
    ∃ a b c : K, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ h = (X - C a) * (X - C b) * (X - C c) := by
  classical
  have hcard : h.roots.card = 3 := by rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hnodup : h.roots.Nodup := Polynomial.nodup_roots hsep
  obtain ⟨a, b, c, hs⟩ := Multiset.card_eq_three.1 hcard
  have hprod : h = (h.roots.map fun x => X - C x).prod :=
    Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits h) hm
  rw [hs] at hnodup hprod
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
    Multiset.prod_singleton] at hprod
  simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or] at hnodup
  obtain ⟨⟨hab, hac⟩, hbc⟩ := hnodup
  exact ⟨a, b, c, hab, hac, hbc, by rw [hprod]; ring⟩
/-- **Powerful values of a separable cubic.**  Over an algebraically closed field of
characteristic zero, if `x^p y^q = f(z)` with `p, q ≥ 2` and `f` a monic separable cubic, then
`x`, `y` and `z` are constant. -/
theorem constant_of_pow_mul_pow_eq_separable_cubic {f : K[X]} (hm : f.Monic)
    (hdeg : f.natDegree = 3) (hsep : f.Separable) {x y z : K[X]} {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p * y ^ q = Polynomial.aeval z f) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hfac⟩ := exists_three_distinct_roots hm hdeg hsep
  refine constant_of_pow_mul_pow_eq_split_cubic hp hq hx hy (one_ne_zero) hab hac hbc ?_
  rw [h, hfac]
  simp
/-! ## The two remaining cubic equations of Table 12 -/
/-- `x³ y² = z³ − z + 1` has no nonconstant polynomial solutions over `ℚ`. -/
theorem cubeSubXAddOne_constant {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 3 - z + 1) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  classical
  set φ := algebraMap ℚ ℂ with hφ
  have hinj : Function.Injective φ := (algebraMap ℚ ℂ).injective
  have hmap : (x.map φ) ^ 3 * (y.map φ) ^ 2
      = Polynomial.aeval (z.map φ) (X ^ 3 - X + 1 : ℂ[X]) := by
    have := congrArg (Polynomial.map φ) h
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_one] at this
    rw [this]
    simp
  have hsep : (X ^ 3 - X + 1 : ℂ[X]).Separable := by
    refine ⟨C (1 / 23) * (18 * X + 27), C (1 / 23) * (-6 * X ^ 2 - 9 * X + 4), ?_⟩
    have hder : derivative (X ^ 3 - X + 1 : ℂ[X]) = 3 * X ^ 2 - 1 := by
      simp [C_ofNat]; norm_num
    have key : (18 * X + 27) * (X ^ 3 - X + 1 : ℂ[X])
        + (-6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 - 1) = (23 : ℂ[X]) := by ring
    rw [hder]
    calc C (1 / 23) * (18 * X + 27) * (X ^ 3 - X + 1 : ℂ[X])
          + C (1 / 23) * (-6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 - 1)
        = C (1 / 23) * ((18 * X + 27) * (X ^ 3 - X + 1)
            + (-6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 - 1)) := by ring
      _ = C (1 / 23) * (23 : ℂ[X]) := by rw [key]
      _ = 1 := by rw [← C_ofNat 23, ← map_mul]; norm_num
  have hm : (X ^ 3 - X + 1 : ℂ[X]).Monic := by monicity!
  have hdeg : (X ^ 3 - X + 1 : ℂ[X]).natDegree = 3 := by compute_degree!
  obtain ⟨h1, h2, h3⟩ := constant_of_pow_mul_pow_eq_separable_cubic hm hdeg hsep
    (by norm_num) (by norm_num) (by simpa [Polynomial.map_eq_zero_iff hinj] using hx)
    (by simpa [Polynomial.map_eq_zero_iff hinj] using hy) hmap
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at h1 h2 h3
  exact ⟨h1, h2, h3⟩
/-- `x³ y² = z³ + z + 1` has no nonconstant polynomial solutions over `ℚ`. -/
theorem cubeAddXAddOne_constant {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 3 + z + 1) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  classical
  set φ := algebraMap ℚ ℂ with hφ
  have hinj : Function.Injective φ := (algebraMap ℚ ℂ).injective
  have hmap : (x.map φ) ^ 3 * (y.map φ) ^ 2
      = Polynomial.aeval (z.map φ) (X ^ 3 + X + 1 : ℂ[X]) := by
    have := congrArg (Polynomial.map φ) h
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_one] at this
    rw [this]
    simp
  have hsep : (X ^ 3 + X + 1 : ℂ[X]).Separable := by
    refine ⟨C (1 / 31) * (-18 * X + 27), C (1 / 31) * (6 * X ^ 2 - 9 * X + 4), ?_⟩
    have hder : derivative (X ^ 3 + X + 1 : ℂ[X]) = 3 * X ^ 2 + 1 := by
      simp [C_ofNat]; norm_num
    have key : (-18 * X + 27) * (X ^ 3 + X + 1 : ℂ[X])
        + (6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 + 1) = (31 : ℂ[X]) := by ring
    rw [hder]
    calc C (1 / 31) * (-18 * X + 27) * (X ^ 3 + X + 1 : ℂ[X])
          + C (1 / 31) * (6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 + 1)
        = C (1 / 31) * ((-18 * X + 27) * (X ^ 3 + X + 1)
            + (6 * X ^ 2 - 9 * X + 4) * (3 * X ^ 2 + 1)) := by ring
      _ = C (1 / 31) * (31 : ℂ[X]) := by rw [key]
      _ = 1 := by rw [← C_ofNat 31, ← map_mul]; norm_num
  have hm : (X ^ 3 + X + 1 : ℂ[X]).Monic := by monicity!
  have hdeg : (X ^ 3 + X + 1 : ℂ[X]).natDegree = 3 := by compute_degree!
  obtain ⟨h1, h2, h3⟩ := constant_of_pow_mul_pow_eq_separable_cubic hm hdeg hsep
    (by norm_num) (by norm_num) (by simpa [Polynomial.map_eq_zero_iff hinj] using hx)
    (by simpa [Polynomial.map_eq_zero_iff hinj] using hy) hmap
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at h1 h2 h3
  exact ⟨h1, h2, h3⟩
end FunctionField
