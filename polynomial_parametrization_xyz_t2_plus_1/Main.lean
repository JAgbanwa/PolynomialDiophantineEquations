import Mathlib
set_option autoImplicit false
/-!
# A polynomial parametrization of `x * y * z + t ^ 2 + 1 = 0`
This file formalizes the algebraic parametrization in the supplied paper.  The
four coordinate functions below are integer polynomials in the three
parameters `a`, `b`, and `c`.
-/
namespace PolynomialParametrization
/-- The elementary norm-splitting identity used twice by the construction. -/
theorem norm_splitting {A : Type*} [CommRing A] (U V : A) :
    (U + V * (U ^ 2 + 1)) ^ 2 + 1 =
      (U ^ 2 + 1) * ((1 + U * V) ^ 2 + V ^ 2) := by
  ring
/-- The full construction is a polynomial identity over every commutative ring.
This is the formal counterpart of the claim that the displayed formulas belong
to `ℤ[a,b,c]` and satisfy the equation identically. -/
theorem universal_parametrization_identity {A : Type*} [CommRing A] (a b c : A) :
    let r := a + b * (a ^ 2 + 1)
    let x := -((1 + c * r) ^ 2 + c ^ 2)
    let y := (1 + a * b) ^ 2 + b ^ 2
    let z := a ^ 2 + 1
    let t := r + c * (r ^ 2 + 1)
    x * y * z + t ^ 2 + 1 = 0 := by
  dsimp
  ring
/-- The intermediate polynomial `R = a + b(a²+1)`. -/
def R (a b : ℤ) : ℤ := a + b * (a ^ 2 + 1)
/-- The `x` coordinate of the parametrization. -/
def X (a b c : ℤ) : ℤ := -((1 + c * R a b) ^ 2 + c ^ 2)
/-- The `y` coordinate of the parametrization. -/
def Y (a b : ℤ) : ℤ := (1 + a * b) ^ 2 + b ^ 2
/-- The `z` coordinate of the parametrization. -/
def Z (a : ℤ) : ℤ := a ^ 2 + 1
/-- The `t` coordinate of the parametrization. -/
def T (a b c : ℤ) : ℤ := R a b + c * ((R a b) ^ 2 + 1)
/-- The first use of norm splitting factors `R²+1` as `Z*Y`. -/
theorem R_sq_add_one (a b : ℤ) :
    (R a b) ^ 2 + 1 = Z a * Y a b := by
  simpa [R, Z, Y] using norm_splitting a b
/-- The advertised polynomial coordinates satisfy the Diophantine equation
identically for all integer parameters. -/
theorem parametrization_equation (a b c : ℤ) :
    X a b c * Y a b * Z a + (T a b c) ^ 2 + 1 = 0 := by
  have h := norm_splitting (R a b) c
  rw [R_sq_add_one] at h
  simp only [X, T]
  rw [R_sq_add_one]
  nlinarith
/-- Every specialization has the signs asserted in the paper. -/
theorem parametrization_signs (a b c : ℤ) :
    X a b c < 0 ∧ 0 < Y a b ∧ 0 < Z a := by
  constructor
  · have h : 0 < (1 + c * R a b) ^ 2 + c ^ 2 := by
      by_cases hc : c = 0
      · subst c
        norm_num
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hc)
    simpa [X] using (neg_lt_zero.mpr h)
  constructor
  · by_cases hb : b = 0
    · subst b
      norm_num [Y]
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by norm_num)
/-- The one-parameter specialization from the paper. -/
def oneParameter (n : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (-((n ^ 2 - n) ^ 2 + 1),
    (n - 1) ^ 2 + 1,
    n ^ 2 + 1,
    n ^ 4 - 2 * n ^ 3 + 2 * n ^ 2 - n + 1)
/-- The explicit one-parameter family also solves the equation. -/
theorem oneParameter_equation (n : ℤ) :
    let p := oneParameter n
    p.1 * p.2.1 * p.2.2.1 + p.2.2.2 ^ 2 + 1 = 0 := by
  simp only [oneParameter]
  ring
/-- At `n = 2`, the family gives the example `(-5, 2, 5, 7)`. -/
theorem oneParameter_two : oneParameter 2 = (-5, 2, 5, 7) := by
  native_decide
end PolynomialParametrization
