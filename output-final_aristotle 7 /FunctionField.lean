import Mathlib
/-!
# Function-field analogues of the open equations of Tables 11–13
B. Grechuk, *A systematic approach to Diophantine equations: open problems*, lists a
number of small Diophantine equations for which the following questions are open:
* **Problem 4** — does the equation have an integer solution?
* **Problem 6** — same question for the three-monomial equations of Table 13;
* **Problem 7** — does it have a solution in positive integers?
* **Problem 2** — is `min(|x|, |y|, |z|)` unbounded on the solution set?
A standard way in which such questions get a positive answer is a *polynomial identity*: a
parametric family `x(t), y(t), z(t)` of solutions.  This file proves, unconditionally, that
**no such family exists** for a large list of these equations: over any field of
characteristic zero, every polynomial solution is constant.
The engine is the Mason–Stothers theorem (`Polynomial.abc` in Mathlib), in the following
shape.
## Main results
* `FunctionField.constant_of_pow_mul_pow_eq` — if `a x^p y^q = b z^r + c` holds in `k[X]`
  with `a, b, c` nonzero constants, `p, q, r ≥ 2` and `x, y ≠ 0`, then `x`, `y`, `z` are
  all constant.
* Corollaries for the four equations of Table 13 (Problem 6 is open for all of them):
  `cubeAddSix`, `quarticAddTwo`, `quarticSubThree` for `x³y² = z³+6`, `z⁴+2`, `z⁴−3`, and
  `sqAddThree` for `x⁴y³ = z²+3`; also `twoCubeAddOne` for `x³y² = 2z³+1`.
* Corollaries for the Table 11 equations, whose reductions are carried out in
  `RequestProject.Table11`:
  `eqC_polynomial_constant`  : `y (x³ − z²) = z`     has only constant polynomial
                               solutions besides the trivial family `y = z = 0`;
  `eqA_polynomial_constant`  : `y (x³ − z²) = x`     likewise (trivial family `x = z = 0`);
  `eq11b_polynomial_constant`: `x² y² + x = z³`      likewise (trivial family `x = z = 0`).
Consequently, for all of these equations a positive answer to the corresponding open
problem cannot come from a polynomial identity.  (The method does *not* cover the two
remaining Table 11 equations `y(x³ − z²) = x + 1`, nor the Table 5 equation
`y² + x²y + z²x = 2`; see `FINDINGS.md`.)
-/
open Polynomial UniqueFactorizationMonoid
namespace FunctionField
variable {k : Type*} [Field k] [CharZero k] [DecidableEq k]
/-! ## The main Mason–Stothers estimate -/
/-- **Main theorem.**  Let `k` be a field of characteristic zero and let `p, q, r ≥ 2`.
If nonzero polynomials `x, y ∈ k[X]` and `z ∈ k[X]` satisfy
`a · x^p · y^q = b · z^r + c` for nonzero constants `a, b, c`, then `x`, `y` and `z` are
all constant.
In other words, the equation `a x^p y^q = b z^r + c` admits no nonconstant polynomial
family of solutions. -/
theorem constant_of_pow_mul_pow_eq (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) {x y z : k[X]}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : C a * x ^ p * y ^ q = C b * z ^ r + C c) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  have key : ∀ m n : ℕ, 2 ≤ m → m * n = 0 → n = 0 := by
    intro m n hm hmn
    rcases Nat.mul_eq_zero.1 hmn with h' | h'
    · omega
    · exact h'
  have hnb : (-b) ≠ 0 := neg_ne_zero.2 hb
  have hnc : (-c) ≠ 0 := neg_ne_zero.2 hc
  have hCa0 : (C a : k[X]) ≠ 0 := by simpa using ha
  have hCb0 : (C (-b) : k[X]) ≠ 0 := by simpa using hnb
  have hxp : x ^ p ≠ 0 := pow_ne_zero _ hx
  have hyq : y ^ q ≠ 0 := pow_ne_zero _ hy
  have hA0 : C a * x ^ p * y ^ q ≠ 0 := mul_ne_zero (mul_ne_zero hCa0 hxp) hyq
  have hdegA : (C a * x ^ p * y ^ q).natDegree = p * x.natDegree + q * y.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCa0 hxp) hyq, natDegree_mul hCa0 hxp, natDegree_C,
      natDegree_pow, natDegree_pow, zero_add]
  by_cases hz : z = 0
  · subst hz
    have heq : C a * x ^ p * y ^ q = C c := by
      simpa [zero_pow (by omega : r ≠ 0)] using h
    have hd : p * x.natDegree + q * y.natDegree = 0 := by
      rw [← hdegA, heq, natDegree_C]
    exact ⟨key p _ hp (by omega), key q _ hq (by omega), by simp⟩
  set A : k[X] := C a * x ^ p * y ^ q with hAdef
  set B : k[X] := C (-b) * z ^ r with hBdef
  set D : k[X] := C (-c) with hDdef
  have hB0 : B ≠ 0 := mul_ne_zero hCb0 (pow_ne_zero _ hz)
  have hD0 : D ≠ 0 := by rw [hDdef]; simpa using hnc
  have hsum : A + B + D = 0 := by
    rw [h, hBdef, hDdef, map_neg, map_neg]; ring
  have hdegB : B.natDegree = r * z.natDegree := by
    rw [hBdef, natDegree_mul hCb0 (pow_ne_zero _ hz), natDegree_C, natDegree_pow, zero_add]
  have hcop : IsCoprime A B := by
    refine ⟨C c⁻¹, C c⁻¹, ?_⟩
    have hAB : A + B = C c := by
      have hDc : D = -C c := by rw [hDdef, map_neg]
      linear_combination hsum - hDc
    calc C c⁻¹ * A + C c⁻¹ * B = C c⁻¹ * (A + B) := by ring
      _ = C c⁻¹ * C c := by rw [hAB]
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  rcases Polynomial.abc hA0 hB0 hD0 hcop hsum with ⟨h1, h2, _⟩ | ⟨d1, d2, _⟩
  · exfalso
    have hrad : radical (A * B * D) ∣ radical x * radical y * radical z := by
      refine dvd_trans radical_mul_dvd ?_
      have hD : radical D = 1 := by
        rw [hDdef]; exact radical_of_isUnit (isUnit_C.2 hnc.isUnit)
      rw [hD, mul_one]
      refine dvd_trans radical_mul_dvd ?_
      have hRA : radical A = radical (x ^ p * y ^ q) := by
        rw [hAdef, mul_assoc, radical_mul_of_isUnit_left (isUnit_C.2 ha.isUnit)]
      have hRB : radical B = radical z := by
        rw [hBdef, radical_mul_of_isUnit_left (isUnit_C.2 hnb.isUnit), radical_pow _ (by omega)]
      rw [hRA, hRB]
      exact mul_dvd_mul_right (dvd_trans radical_mul_dvd
        (by rw [radical_pow _ (by omega : p ≠ 0), radical_pow _ (by omega : q ≠ 0)])) _
    have hle : (radical (A * B * D)).natDegree ≤ x.natDegree + y.natDegree + z.natDegree := by
      refine le_trans (natDegree_le_of_dvd hrad
        (mul_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero)) ?_
      rw [natDegree_mul (mul_ne_zero radical_ne_zero radical_ne_zero) radical_ne_zero,
        natDegree_mul radical_ne_zero radical_ne_zero]
      exact Nat.add_le_add (Nat.add_le_add natDegree_radical_le natDegree_radical_le)
        natDegree_radical_le
    rw [hdegA] at h1
    rw [hdegB] at h2
    have e1 : 2 * x.natDegree ≤ p * x.natDegree := Nat.mul_le_mul_right _ hp
    have e2 : 2 * y.natDegree ≤ q * y.natDegree := Nat.mul_le_mul_right _ hq
    have e3 : 2 * z.natDegree ≤ r * z.natDegree := Nat.mul_le_mul_right _ hr
    omega
  · have hA' : A.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero d1
    have hB' : B.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero d2
    rw [hdegA] at hA'
    rw [hdegB] at hB'
    exact ⟨key p _ hp (by omega), key q _ hq (by omega), key r _ hr hB'⟩
/-- Monic version of `constant_of_pow_mul_pow_eq`: `x^p y^q = z^r + c`. -/
theorem constant_of_pow_mul_pow_eq_add_const (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    {c : k} (hc : c ≠ 0) {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p * y ^ q = z ^ r + C c) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  refine constant_of_pow_mul_pow_eq p q r hp hq hr (one_ne_zero) (one_ne_zero) hc hx hy ?_
  simpa using h
/-! ## Table 13: the equations `x^a y^b = f(z)` for which Problem 6 is open -/
/-- Equation (27) of the paper, `x³y² = z³ + 6`, the smallest three-monomial equation of
unknown solvability, has no nonconstant polynomial solutions. -/
theorem cubeAddSix_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 3 + C 6) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 3 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hx hy h
/-- `x³y² = z⁴ + 2` has no nonconstant polynomial solutions. -/
theorem quarticAddTwo_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 4 + C 2) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 3 2 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hx hy h
/-- `x³y² = z⁴ − 3` has no nonconstant polynomial solutions. -/
theorem quarticSubThree_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 4 - C 3) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  refine constant_of_pow_mul_pow_eq_add_const 3 2 4 (by norm_num) (by norm_num) (by norm_num)
    (show (-3 : k) ≠ 0 by norm_num) hx hy ?_
  rw [h, map_neg]; ring
/-- `x⁴y³ = z² + 3` has no nonconstant polynomial solutions. -/
theorem sqAddThree_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 4 * y ^ 3 = z ^ 2 + C 3) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 4 3 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hx hy h
/-- `x³y² = 2z³ + 1` has no nonconstant polynomial solutions. -/
theorem twoCubeAddOne_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = C 2 * z ^ 3 + C 1) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 := by
  refine constant_of_pow_mul_pow_eq 3 2 3 (by norm_num) (by norm_num) (by norm_num)
    (one_ne_zero) (show (2 : k) ≠ 0 by norm_num) (one_ne_zero) hx hy ?_
  simpa using h
/-! ### Table 12: equations of the same shape for which Problem 4 is open -/
/-- `x³y² = z⁴ + 1` has no nonconstant polynomial solutions. -/
theorem quarticAddOne_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 4 + C 1) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 3 2 4 (by norm_num) (by norm_num) (by norm_num)
    (one_ne_zero) hx hy h
/-- `x³y² = z³ + 2` has no nonconstant polynomial solutions. -/
theorem cubeAddTwo_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 3 + C 2) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 3 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hx hy h
/-- `x⁴y³ = z² + 1` has no nonconstant polynomial solutions. -/
theorem sqAddOne_constant {x y z : k[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 4 * y ^ 3 = z ^ 2 + C 1) :
    x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0 :=
  constant_of_pow_mul_pow_eq_add_const 4 3 2 (by norm_num) (by norm_num) (by norm_num)
    (one_ne_zero) hx hy h
/-- Restatement of `cubeAddSix_constant` over `ℚ`: a polynomial parametrisation
`(x(t), y(t), z(t))` of solutions of the open equation `x³y² = z³ + 6` is necessarily a
constant one. -/
theorem cubeAddSix_eq_C {x y z : ℚ[X]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 3 * y ^ 2 = z ^ 3 + C 6) :
    ∃ a b c : ℚ, x = C a ∧ y = C b ∧ z = C c := by
  obtain ⟨h1, h2, h3⟩ := cubeAddSix_constant hx hy h
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 h1
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.1 h2
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 h3
  exact ⟨a, b, c, ha.symm, hb.symm, hc.symm⟩
/-! ## Table 11: the equations for which Problems 2 and 7 are open
The three equations below are (A) `y(x³ − z²) = x`, (C) `y(x³ − z²) = z` and its companion
(11)(b) `x²y² + x = z³`.  Each of them has *some* nonconstant polynomial solutions, but only
the degenerate ones listed in the statements; in particular no polynomial family can make
`min(|x|, |y|, |z|)` unbounded, and none produces solutions in positive integers. -/
omit [CharZero k] [DecidableEq k] in
/-- Coprime factors of an `N`-th power in `k[X]` are `N`-th powers up to a constant. -/
theorem exists_C_mul_pow_of_isCoprime {m n c : k[X]} {N : ℕ} (hco : IsCoprime m n)
    (h : m * n = c ^ N) : ∃ (α : k) (e : k[X]), α ≠ 0 ∧ m = C α * e ^ N := by
  obtain ⟨e, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco h
  obtain ⟨α, hα, hCα⟩ := Polynomial.isUnit_iff.1 u.isUnit
  exact ⟨α, e, hα.ne_zero, by rw [← hu, hCα, mul_comm]⟩
/-- Equation (C) `y (x³ − z²) = z` (equation (11)(a) of the paper).  Every polynomial
solution is either degenerate (`z = 0` together with `y = 0` or `x = 0`) or constant. -/
theorem eqC_polynomial_constant {x y z : k[X]} (h : y * (x ^ 3 - z ^ 2) = z) :
    (y = 0 ∧ z = 0) ∨ (x = 0 ∧ z = 0) ∨
      (x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0) := by
  by_cases hy : y = 0
  · left; exact ⟨hy, by simpa [hy] using h.symm⟩
  right
  set d : k[X] := x ^ 3 - z ^ 2 with hd
  have hzz : z = y * d := h.symm
  have hx3 : d * (y ^ 2 * d + 1) = x ^ 3 := by
    have hxx : x ^ 3 = d + z ^ 2 := by rw [hd]; ring
    rw [hxx, hzz]; ring
  have hco : IsCoprime d (y ^ 2 * d + 1) := ⟨-y ^ 2, 1, by ring⟩
  obtain ⟨α, e, hα, hde⟩ := exists_C_mul_pow_of_isCoprime hco hx3
  obtain ⟨β, f, hβ, hf⟩ := exists_C_mul_pow_of_isCoprime hco.symm (by rw [mul_comm]; exact hx3)
  by_cases he : e = 0
  · have hd0 : d = 0 := by rw [hde, he]; simp
    have hz0 : z = 0 := by rw [hzz, hd0, mul_zero]
    have hx0 : x = 0 := by
      have hc3 : x ^ 3 = 0 := by rw [← hx3, hd0, zero_mul]
      exact pow_eq_zero_iff (by norm_num) |>.1 hc3
    exact Or.inl ⟨hx0, hz0⟩
  · right
    have hmain : C α * y ^ 2 * e ^ 3 = C β * f ^ 3 + C (-1) := by
      have h1 : C β * f ^ 3 = y ^ 2 * (C α * e ^ 3) + 1 := by rw [← hde, ← hf]
      rw [map_neg, map_one, h1]; ring
    obtain ⟨hY, hE, hF⟩ := constant_of_pow_mul_pow_eq 2 3 3 le_rfl (by norm_num) (by norm_num)
      hα hβ (by norm_num : (-1 : k) ≠ 0) hy he hmain
    have hdd : d.natDegree = 0 := by
      rw [hde]
      have hle := natDegree_mul_le (p := (C α : k[X])) (q := e ^ 3)
      simp [natDegree_pow, hE] at hle ⊢
      omega
    have hzd : z.natDegree = 0 := by
      rw [hzz]
      have hle := natDegree_mul_le (p := y) (q := d)
      omega
    have hxd : x.natDegree = 0 := by
      have h3 : (x ^ 3).natDegree = 3 * x.natDegree := natDegree_pow _ _
      have h4 : (x ^ 3).natDegree ≤ d.natDegree + (y ^ 2 * d + 1).natDegree := by
        rw [← hx3]; exact natDegree_mul_le
      have h5 : (y ^ 2 * d + 1).natDegree = 0 := by
        rw [hf]
        have hle := natDegree_mul_le (p := (C β : k[X])) (q := f ^ 3)
        simp [natDegree_pow, hF] at hle ⊢
        omega
      omega
    exact ⟨hxd, hY, hzd⟩
/-- Equation (A) `y (x³ − z²) = x` (equation (12) of the paper).  Every polynomial solution
is either degenerate (`x = 0` together with `y = 0` or `z = 0`) or constant. -/
theorem eqA_polynomial_constant {x y z : k[X]} (h : y * (x ^ 3 - z ^ 2) = x) :
    (x = 0 ∧ y = 0) ∨ (x = 0 ∧ z = 0) ∨
      (x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0) := by
  by_cases hy : y = 0
  · left; exact ⟨by simpa [hy] using h.symm, hy⟩
  right
  set d : k[X] := x ^ 3 - z ^ 2 with hd
  have hxx : x = y * d := h.symm
  have hz2 : d * (y ^ 3 * d ^ 2 - 1) = z ^ 2 := by
    have hzz : z ^ 2 = x ^ 3 - d := by rw [hd]; ring
    rw [hzz, hxx]; ring
  have hco : IsCoprime d (y ^ 3 * d ^ 2 - 1) := ⟨y ^ 3 * d, -1, by ring⟩
  obtain ⟨α, e, hα, hde⟩ := exists_C_mul_pow_of_isCoprime hco hz2
  obtain ⟨β, f, hβ, hf⟩ := exists_C_mul_pow_of_isCoprime hco.symm (by rw [mul_comm]; exact hz2)
  by_cases he : e = 0
  · have hd0 : d = 0 := by rw [hde, he]; simp
    have hx0 : x = 0 := by rw [hxx, hd0, mul_zero]
    have hz0 : z = 0 := by
      have hc2 : z ^ 2 = 0 := by rw [← hz2, hd0, zero_mul]
      exact pow_eq_zero_iff (by norm_num) |>.1 hc2
    exact Or.inl ⟨hx0, hz0⟩
  · right
    have hmain : C (α ^ 2) * y ^ 3 * e ^ 4 = C β * f ^ 2 + C 1 := by
      have h1 : C β * f ^ 2 = y ^ 3 * (C α * e ^ 2) ^ 2 - 1 := by rw [← hde, ← hf]
      rw [map_one, h1, map_pow]; ring
    obtain ⟨hY, hE, hF⟩ := constant_of_pow_mul_pow_eq 3 4 2 (by norm_num) (by norm_num) le_rfl
      (pow_ne_zero 2 hα) hβ (one_ne_zero) hy he hmain
    have hdd : d.natDegree = 0 := by
      rw [hde]
      have hle := natDegree_mul_le (p := (C α : k[X])) (q := e ^ 2)
      simp [natDegree_pow, hE] at hle ⊢
      omega
    have hxd : x.natDegree = 0 := by
      rw [hxx]
      have hle := natDegree_mul_le (p := y) (q := d)
      omega
    have hzd : z.natDegree = 0 := by
      have h3 : (z ^ 2).natDegree = 2 * z.natDegree := natDegree_pow _ _
      have h4 : (z ^ 2).natDegree ≤ d.natDegree + (y ^ 3 * d ^ 2 - 1).natDegree := by
        rw [← hz2]; exact natDegree_mul_le
      have h5 : (y ^ 3 * d ^ 2 - 1).natDegree = 0 := by
        rw [hf]
        have hle := natDegree_mul_le (p := (C β : k[X])) (q := f ^ 2)
        simp [natDegree_pow, hF] at hle ⊢
        omega
      omega
    exact ⟨hxd, hY, hzd⟩
/-- Equation (11)(b) `x² y² + x = z³`.  Every polynomial solution is either degenerate
(`x = z = 0`, or `y = 0` and `x = z³`) or constant. -/
theorem eq11b_polynomial_constant {x y z : k[X]} (h : x ^ 2 * y ^ 2 + x = z ^ 3) :
    (x = 0 ∧ z = 0) ∨ (y = 0 ∧ x = z ^ 3) ∨
      (x.natDegree = 0 ∧ y.natDegree = 0 ∧ z.natDegree = 0) := by
  by_cases hx : x = 0
  · left
    refine ⟨hx, ?_⟩
    have hc3 : z ^ 3 = 0 := by rw [← h, hx]; ring
    exact (pow_eq_zero_iff (by norm_num)).1 hc3
  by_cases hy : y = 0
  · right; left; exact ⟨hy, by rw [← h, hy]; ring⟩
  right; right
  have hfac : x * (x * y ^ 2 + 1) = z ^ 3 := by rw [← h]; ring
  have hco : IsCoprime x (x * y ^ 2 + 1) := ⟨-y ^ 2, 1, by ring⟩
  obtain ⟨α, e, hα, hxe⟩ := exists_C_mul_pow_of_isCoprime hco hfac
  obtain ⟨β, f, hβ, hf⟩ := exists_C_mul_pow_of_isCoprime hco.symm (by rw [mul_comm]; exact hfac)
  have he : e ≠ 0 := by
    intro h0; apply hx; rw [hxe, h0]; simp
  have hmain : C α * y ^ 2 * e ^ 3 = C β * f ^ 3 + C (-1) := by
    have h1 : C β * f ^ 3 = C α * e ^ 3 * y ^ 2 + 1 := by rw [← hxe, ← hf]
    rw [map_neg, map_one, h1]; ring
  obtain ⟨hY, hE, hF⟩ := constant_of_pow_mul_pow_eq 2 3 3 le_rfl (by norm_num) (by norm_num)
    hα hβ (by norm_num : (-1 : k) ≠ 0) hy he hmain
  have hxd : x.natDegree = 0 := by
    rw [hxe]
    have hle := natDegree_mul_le (p := (C α : k[X])) (q := e ^ 3)
    simp [natDegree_pow, hE] at hle ⊢
    omega
  have hzd : z.natDegree = 0 := by
    have h3 : (z ^ 3).natDegree = 3 * z.natDegree := natDegree_pow _ _
    have h4 : (z ^ 3).natDegree ≤ x.natDegree + (x * y ^ 2 + 1).natDegree := by
      rw [← hfac]; exact natDegree_mul_le
    have h5 : (x * y ^ 2 + 1).natDegree = 0 := by
      rw [hf]
      have hle := natDegree_mul_le (p := (C β : k[X])) (q := f ^ 3)
      simp [natDegree_pow, hF] at hle ⊢
      omega
    omega
  exact ⟨hxd, hY, hzd⟩
end FunctionField
