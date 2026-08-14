import Mathlib
/-!
# The three shortest equations for which Problem 2 is open
Table 11 of B. Grechuk, *A systematic approach to Diophantine equations: open problems*,
lists the equations of length `l ≤ 8` for which **Problem 2** ("is
`min(|x|, |y|, |z|)` unbounded over the solution set?") is open:
* (A)  `y (x³ - z²) = x`
* (B)  `y (x³ - z²) = x + 1`
* (C)  `y (x³ - z²) = z`
This file gives complete, machine-checked **reductions** of these three equations to
much more transparent families, together with explicit solutions.
## Main results
* `Table11.eqC_iff`: `(x, y, z)` solves (C) **iff** there are `e, f` with
  `x = e f`, `z = y e³` and `f³ = y² e³ + 1`.  So (C) is equivalent to the family of
  Thue-type equations `f³ - y² e³ = 1`, and Problem 2 for (C) is precisely the
  question whether that family has solutions with `|y|` and `|e f|` arbitrarily large.
* `Table11.eqA_iff`: `(x, y, z)` solves (A) **iff** there are an integer `a` and a
  sign `ε` with `x = ε y a²` and `ε z² = a² (y³ a⁴ - 1)`.
* `Table11.eqB_iff`: (B) is solvable for a given `x` **iff** `x + 1` has a nonzero
  divisor `d` for which `x³ - d` is a perfect square.
* `Table11.problem2A_le`, `Table11.problem2B_le`, `Table11.problem2C_le`: explicit
  solutions showing that Problem 2 has a positive answer for all `k` below `2`, `9`
  and `39` respectively.  (For these equations `x³ - z²` divides a number of absolute
  value at most `|x| + 1`, resp. `|z|`, which forces `z` to be the integer nearest to
  `x^{3/2}`; an exhaustive computer search of that shape over `1 ≤ x ≤ 8·10¹⁰`
  produced no solution with a larger value of `min(|x|, |y|, |z|)`.)
* `Table11.problem2C_iff`: Problem 2 for (C) has a positive answer **iff** the family
  `f³ - y² e³ = 1` has solutions with `|y|` and `|e f|` arbitrarily large.
Equations (A) and (C) are also equations (12) and (11)(a) of the paper, of size `H = 26`:
they are among the smallest equations for which **Problem 7** (existence of a solution in
*positive* integers) is open.  The reductions specialise to that question:
* `Table11.problem7C_iff`: `y (x³ - z²) = z` has a positive solution iff `f³ = y² e³ + 1`
  has one;
* `Table11.problem7A_iff`: `y (x³ - z²) = x` has a positive solution iff `b² = y³ a⁴ - 1`
  has one;
* `Table11.eq11b_iff` and `Table11.problem7_11b_iff`: the companion equation (11)(b),
  `x² y² + x = z³`, reduces to the *same* family `f³ = y² e³ + 1`, which is the precise
  form of the paper's remark that (11)(a) and (11)(b) are reducible to one another.
All these problems remain open; the reductions and the criteria isolate exactly what
is missing.
-/
namespace Table11
/-! ## Two factorisation lemmas -/
/-- Coprime factors of a cube in `ℤ` are cubes. -/
theorem cube_of_coprime_mul {d m c : ℤ} (hco : IsCoprime d m) (h : d * m = c ^ 3) :
    ∃ e : ℤ, d = e ^ 3 := by
  obtain ⟨e, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco h
  rcases Int.isUnit_iff.1 u.isUnit with h1 | h1
  · exact ⟨e, by rw [← hu, h1]; ring⟩
  · exact ⟨-e, by rw [← hu, h1]; ring⟩
/-- Coprime factors of a square in `ℤ` are squares up to sign. -/
theorem sq_of_coprime_mul {d m c : ℤ} (hco : IsCoprime d m) (h : d * m = c ^ 2) :
    ∃ a : ℤ, d = a ^ 2 ∨ d = -a ^ 2 := by
  obtain ⟨a, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco h
  rcases Int.isUnit_iff.1 u.isUnit with h1 | h1
  · exact ⟨a, Or.inl (by rw [← hu, h1]; ring)⟩
  · exact ⟨a, Or.inr (by rw [← hu, h1]; ring)⟩
/-! ## Equation (C):  `y (x³ - z²) = z` -/
/-- **Reduction of equation (C).**  `y (x³ - z²) = z` holds iff `x = e f`, `z = y e³`
and `f³ = y² e³ + 1` for some integers `e, f`. -/
theorem eqC_iff (x y z : ℤ) :
    y * (x ^ 3 - z ^ 2) = z ↔ ∃ e f : ℤ, x = e * f ∧ z = y * e ^ 3 ∧ f ^ 3 = y ^ 2 * e ^ 3 + 1 := by
  constructor
  · intro h
    have hz : z = y * (x ^ 3 - z ^ 2) := h.symm
    have hcube : (x ^ 3 - z ^ 2) * (y ^ 2 * (x ^ 3 - z ^ 2) + 1) = x ^ 3 := by
      linear_combination (-(z + y * (x ^ 3 - z ^ 2))) * hz
    have hco : IsCoprime (x ^ 3 - z ^ 2) (y ^ 2 * (x ^ 3 - z ^ 2) + 1) :=
      ⟨-(y ^ 2), 1, by ring⟩
    obtain ⟨e, he⟩ := cube_of_coprime_mul hco hcube
    rcases eq_or_ne e 0 with rfl | he0
    · have hd0 : x ^ 3 - z ^ 2 = 0 := by simpa using he
      have hz0 : z = 0 := by rw [hz, hd0]; ring
      have hx3 : x ^ 3 = 0 := by rw [← hcube, hd0]; ring
      have hx0 : x = 0 := by
        by_contra hx
        exact hx (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hx3)
      exact ⟨0, 1, by rw [hx0]; ring, by rw [hz0]; ring, by norm_num⟩
    · have h3 : e ^ 3 ∣ x ^ 3 := ⟨y ^ 2 * (x ^ 3 - z ^ 2) + 1, by rw [← he]; linarith [hcube]⟩
      obtain ⟨f, hf⟩ := (Int.pow_dvd_pow_iff (n := 3) (by norm_num)).1 h3
      refine ⟨e, f, hf, by rw [hz, he], ?_⟩
      have h1 : e ^ 3 * (y ^ 2 * e ^ 3 + 1) = e ^ 3 * f ^ 3 := by
        have h2 := hcube
        rw [he] at h2
        rw [hf] at h2
        linear_combination h2
      have he3 : (e : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ he0
      have h4 := mul_left_cancel₀ he3 h1
      linarith [h4]
  · rintro ⟨e, f, rfl, rfl, hf⟩
    linear_combination (y * e ^ 3) * hf
/-- **Problem 2 for (C) is *equivalent* to unboundedness in the reduced family.**
The equation `y (x³ - z²) = z` has solutions with `min(|x|, |y|, |z|)` arbitrarily large
if and only if the family `f³ = y² e³ + 1` has solutions with `|y|` and `|e f|`
arbitrarily large. -/
theorem problem2C_iff :
    (∀ k : ℤ, ∃ x y z : ℤ, y * (x ^ 3 - z ^ 2) = z ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z|) ↔
      (∀ k : ℤ, ∃ e f y : ℤ, k ≤ |y| ∧ k ≤ |e * f| ∧ f ^ 3 = y ^ 2 * e ^ 3 + 1) := by
  constructor
  · intro H k
    obtain ⟨x, y, z, hsol, hx, hy, _⟩ := H k
    obtain ⟨e, f, hef, _, hfe⟩ := (eqC_iff x y z).1 hsol
    exact ⟨e, f, y, hy, by rw [← hef]; exact hx, hfe⟩
  · intro H k
    obtain ⟨e, f, y, hy, hef, hfe⟩ := H k
    refine ⟨e * f, y, y * e ^ 3, (eqC_iff _ _ _).2 ⟨e, f, rfl, rfl, hfe⟩, hef, hy, ?_⟩
    rw [abs_mul, abs_pow]
    by_cases h0 : (1 : ℤ) ≤ |e|
    · calc k ≤ |y| := hy
        _ = |y| * 1 := (mul_one _).symm
        _ ≤ |y| * |e| ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ h0) (abs_nonneg y)
    · have he0 : e = 0 := by
        have := abs_nonneg e
        have : |e| = 0 := by omega
        simpa using this
      have hk : k ≤ 0 := by
        have : |e * f| = 0 := by rw [he0]; simp
        exact hef.trans (le_of_eq this)
      calc k ≤ 0 := hk
        _ ≤ |y| * |e| ^ 3 := by positivity
/-- An explicit solution of (C): `(x, y, z) = (46, -39, 312)`, coming from
`e = -2, f = -23` in the reduction, i.e. from `(-23)³ - (-39)² (-2)³ = 1`. -/
theorem solC : (-39 : ℤ) * ((46 : ℤ) ^ 3 - (312 : ℤ) ^ 2) = 312 := by norm_num
/-- **Quantitative form of Problem 2 for (C).**  For every `k ≤ 39` the equation
`y (x³ - z²) = z` has a solution with `min(|x|, |y|, |z|) ≥ k`. -/
theorem problem2C_le {k : ℤ} (hk : k ≤ 39) :
    ∃ x y z : ℤ, y * (x ^ 3 - z ^ 2) = z ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  refine ⟨46, -39, 312, solC, ?_, ?_, ?_⟩
  · rw [show |(46 : ℤ)| = 46 from by norm_num]; linarith
  · rw [show |(-39 : ℤ)| = 39 from by norm_num]; linarith
  · rw [show |(312 : ℤ)| = 312 from by norm_num]; linarith
/-- **Problem 7 for equation (C).**  Equation `y (x³ - z²) = z` — equation (11)(a) of the
paper, of size `H = 26`, one of the smallest equations for which Problem 7 (existence of a
solution in *positive* integers) is open — has a solution in positive integers if and only
if `f³ = y² e³ + 1` has a solution in positive integers. -/
theorem problem7C_iff :
    (∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ y * (x ^ 3 - z ^ 2) = z) ↔
      (∃ e f y : ℤ, 0 < e ∧ 0 < f ∧ 0 < y ∧ f ^ 3 = y ^ 2 * e ^ 3 + 1) := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hsol⟩
    obtain ⟨e, f, hef, hze, hfe⟩ := (eqC_iff x y z).1 hsol
    have hz' : 0 < y * e ^ 3 := by rw [← hze]; exact hz
    have he : 0 < e := by
      by_contra hcon
      push_neg at hcon
      have h3 : e ^ 3 ≤ 0 := by nlinarith [sq_nonneg e]
      nlinarith
    have hx' : 0 < e * f := by rw [← hef]; exact hx
    have hf : 0 < f := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ⟨e, f, y, he, hf, hy, hfe⟩
  · rintro ⟨e, f, y, he, hf, hy, hfe⟩
    exact ⟨e * f, y, y * e ^ 3, mul_pos he hf, hy, by positivity,
      (eqC_iff _ _ _).2 ⟨e, f, rfl, rfl, hfe⟩⟩
/-! ## The companion equation (11)(b) of the paper:  `x² y² + x = z³` -/
/-- **Reduction of equation (11)(b).**  `x² y² + x = z³` holds iff `x = a³`, `z = a b`
and `b³ = a³ y² + 1` for some integers `a, b`.  This is the same reduced family
`f³ = y² e³ + 1` as for equation (C), which is the precise sense in which the paper's
equations (11)(a) and (11)(b) are reducible to one another. -/
theorem eq11b_iff (x y z : ℤ) :
    x ^ 2 * y ^ 2 + x = z ^ 3 ↔ ∃ a b : ℤ, x = a ^ 3 ∧ z = a * b ∧ b ^ 3 = a ^ 3 * y ^ 2 + 1 := by
  constructor
  · intro h
    have hco : IsCoprime x (x * y ^ 2 + 1) := ⟨-(y ^ 2), 1, by ring⟩
    have hcube : x * (x * y ^ 2 + 1) = z ^ 3 := by linear_combination h
    obtain ⟨a, ha⟩ := cube_of_coprime_mul hco hcube
    rcases eq_or_ne a 0 with rfl | ha0
    · have hx0 : x = 0 := by simpa using ha
      have hz0 : z ^ 3 = 0 := by rw [← hcube, hx0]; ring
      have : z = 0 := by
        by_contra hz
        exact hz (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hz0)
      exact ⟨0, 1, by rw [hx0]; ring, by rw [this]; ring, by norm_num⟩
    · have h3 : a ^ 3 ∣ z ^ 3 := ⟨x * y ^ 2 + 1, by rw [← ha]; linarith [hcube]⟩
      obtain ⟨b, hb⟩ := (Int.pow_dvd_pow_iff (n := 3) (by norm_num)).1 h3
      refine ⟨a, b, ha, hb, ?_⟩
      have h1 : a ^ 3 * (a ^ 3 * y ^ 2 + 1) = a ^ 3 * b ^ 3 := by
        have h2 := hcube
        rw [ha] at h2
        rw [hb] at h2
        linear_combination h2
      have ha3 : (a : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ ha0
      linarith [mul_left_cancel₀ ha3 h1]
  · rintro ⟨a, b, rfl, rfl, hb⟩
    linear_combination (-(a ^ 3)) * hb
/-- **Problem 7 for equation (11)(b).**  `x² y² + x = z³` has a solution in positive
integers iff `f³ = y² e³ + 1` does; by `problem7C_iff` this is the same condition as for
equation (C). -/
theorem problem7_11b_iff :
    (∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 * y ^ 2 + x = z ^ 3) ↔
      (∃ e f y : ℤ, 0 < e ∧ 0 < f ∧ 0 < y ∧ f ^ 3 = y ^ 2 * e ^ 3 + 1) := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    obtain ⟨a, b, hxa, hzb, hab⟩ := (eq11b_iff x y z).1 h
    have ha : 0 < a := by
      by_contra hcon
      push_neg at hcon
      have : a ^ 3 ≤ 0 := by nlinarith [sq_nonneg a]
      omega
    have hb : 0 < b := by
      by_contra hcon
      push_neg at hcon
      have hz' : 0 < a * b := by rw [← hzb]; exact hz
      nlinarith
    exact ⟨a, b, y, ha, hb, hy, by linear_combination hab⟩
  · rintro ⟨e, f, y, he, hf, hy, hfe⟩
    refine ⟨e ^ 3, y, e * f, by positivity, hy, mul_pos he hf, ?_⟩
    exact (eq11b_iff _ _ _).2 ⟨e, f, rfl, rfl, by linear_combination hfe⟩
/-! ## Equation (A):  `y (x³ - z²) = x` -/
/-- **Reduction of equation (A).**  `y (x³ - z²) = x` holds iff there are an integer `a`
and a sign `ε` with `x = ε y a²` and `ε z² = a² (y³ a⁴ - 1)`. -/
theorem eqA_iff (x y z : ℤ) :
    y * (x ^ 3 - z ^ 2) = x ↔
      ∃ a eps : ℤ, eps ^ 2 = 1 ∧ x = eps * y * a ^ 2 ∧ eps * z ^ 2 = a ^ 2 * (y ^ 3 * a ^ 4 - 1) := by
  constructor
  · intro h
    have hx : x = y * (x ^ 3 - z ^ 2) := h.symm
    have hsq : (x ^ 3 - z ^ 2) * (y ^ 3 * (x ^ 3 - z ^ 2) ^ 2 - 1) = z ^ 2 := by
      linear_combination (-((y * (x ^ 3 - z ^ 2)) ^ 2 + y * (x ^ 3 - z ^ 2) * x + x ^ 2)) * hx
    have hco : IsCoprime (x ^ 3 - z ^ 2) (y ^ 3 * (x ^ 3 - z ^ 2) ^ 2 - 1) :=
      ⟨y ^ 3 * (x ^ 3 - z ^ 2), -1, by ring⟩
    obtain ⟨a, ha⟩ := sq_of_coprime_mul hco hsq
    rcases ha with ha | ha
    · refine ⟨a, 1, by norm_num, by rw [hx, ha]; ring, ?_⟩
      have h5 := hsq
      rw [ha] at h5
      linear_combination -h5
    · refine ⟨a, -1, by norm_num, by rw [hx, ha]; ring, ?_⟩
      have h5 := hsq
      rw [ha] at h5
      linear_combination h5
  · rintro ⟨a, eps, heps, rfl, hz⟩
    have hz' : z ^ 2 = eps * (a ^ 2 * (y ^ 3 * a ^ 4 - 1)) := by
      linear_combination eps * hz - (z ^ 2) * heps
    calc y * ((eps * y * a ^ 2) ^ 3 - z ^ 2)
        = y * (eps ^ 2 * eps * y ^ 3 * a ^ 6 - z ^ 2) := by ring
      _ = y * (eps * y ^ 3 * a ^ 6 - z ^ 2) := by rw [heps]; ring
      _ = y * (eps * y ^ 3 * a ^ 6 - eps * (a ^ 2 * (y ^ 3 * a ^ 4 - 1))) := by rw [hz']
      _ = eps * y * a ^ 2 := by ring
/-- **Problem 7 for equation (A).**  Equation `y (x³ - z²) = x` — equation (12) of the
paper, of size `H = 26`, one of the smallest equations for which Problem 7 is open — has a
solution in positive integers if and only if `b² = y³ a⁴ - 1` has a solution in positive
integers. -/
theorem problem7A_iff :
    (∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ y * (x ^ 3 - z ^ 2) = x) ↔
      (∃ a b y : ℤ, 0 < a ∧ 0 < b ∧ 0 < y ∧ b ^ 2 = y ^ 3 * a ^ 4 - 1) := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hsol⟩
    obtain ⟨a, eps, heps, hxe, hze⟩ := (eqA_iff x y z).1 hsol
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [hxe] at hx
      simp at hx
    have haa : 0 < a ^ 2 := by positivity
    have heps1 : eps = 1 := by
      have hfac : (eps - 1) * (eps + 1) = 0 := by linear_combination heps
      rcases mul_eq_zero.1 hfac with h | h
      · linarith
      · exfalso
        have hem : eps = -1 := by linarith
        rw [hem] at hxe
        nlinarith [hxe, hx, hy, haa]
    subst heps1
    have hz2 : z ^ 2 = a ^ 2 * (y ^ 3 * a ^ 4 - 1) := by linarith [hze]
    have hdvd : a ∣ z := by
      have h2 : a ^ 2 ∣ z ^ 2 := ⟨y ^ 3 * a ^ 4 - 1, hz2⟩
      exact (Int.pow_dvd_pow_iff (n := 2) (by norm_num)).1 h2
    obtain ⟨b, hb⟩ := hdvd
    have hb2 : b ^ 2 = y ^ 3 * a ^ 4 - 1 := by
      have h3 : a ^ 2 * b ^ 2 = a ^ 2 * (y ^ 3 * a ^ 4 - 1) := by rw [← hz2, hb]; ring
      exact mul_left_cancel₀ (by positivity) h3
    have hbne : b ≠ 0 := by
      intro hb0
      rw [hb, hb0, mul_zero] at hz
      exact lt_irrefl 0 hz
    refine ⟨|a|, |b|, y, abs_pos.2 ha0, abs_pos.2 hbne, hy, ?_⟩
    rw [sq_abs, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a ^ 4)]
    exact hb2
  · rintro ⟨a, b, y, ha, hb, hy, hab⟩
    refine ⟨y * a ^ 2, y, a * b, by positivity, hy, mul_pos ha hb, ?_⟩
    refine (eqA_iff _ _ _).2 ⟨a, 1, by norm_num, by ring, ?_⟩
    rw [one_mul]
    linear_combination (a ^ 2) * hab
/-- An explicit solution of (A): `(x, y, z) = (2, -2, 3)`. -/
theorem solA : (-2 : ℤ) * ((2 : ℤ) ^ 3 - (3 : ℤ) ^ 2) = 2 := by norm_num
/-- **Quantitative form of Problem 2 for (A).**  For every `k ≤ 2` the equation
`y (x³ - z²) = x` has a solution with `min(|x|, |y|, |z|) ≥ k`. -/
theorem problem2A_le {k : ℤ} (hk : k ≤ 2) :
    ∃ x y z : ℤ, y * (x ^ 3 - z ^ 2) = x ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  refine ⟨2, -2, 3, solA, ?_, ?_, ?_⟩
  · rw [show |(2 : ℤ)| = 2 from by norm_num]; linarith
  · rw [show |(-2 : ℤ)| = 2 from by norm_num]; linarith
  · rw [show |(3 : ℤ)| = 3 from by norm_num]; linarith
/-! ## Equation (B):  `y (x³ - z²) = x + 1` -/
/-- **Reduction of equation (B).**  For a given `x`, the equation `y (x³ - z²) = x + 1`
is solvable iff `x + 1` has a nonzero divisor `d` such that `x³ - d` is a perfect square. -/
theorem eqB_iff (x : ℤ) :
    (∃ y z : ℤ, y * (x ^ 3 - z ^ 2) = x + 1) ↔
      ∃ d : ℤ, d ≠ 0 ∧ d ∣ (x + 1) ∧ IsSquare (x ^ 3 - d) := by
  constructor
  · rintro ⟨y, z, h⟩
    refine ⟨x ^ 3 - z ^ 2, ?_, ⟨y, by linarith⟩, ⟨z, by ring⟩⟩
    intro h0
    rw [h0, mul_zero] at h
    have hx : x = -1 := by linarith
    have hz2 : z ^ 2 = -1 := by
      rw [hx] at h0; linarith
    nlinarith [sq_nonneg z]
  · rintro ⟨d, hd0, ⟨y, hy⟩, z, hz⟩
    refine ⟨y, z, ?_⟩
    have hzz : x ^ 3 - z ^ 2 = d := by
      rw [show z * z = z ^ 2 from by ring] at hz; linarith
    rw [hzz, hy]
    ring
/-- An explicit solution of (B): `(x, y, z) = (584, -9, 14113)`. -/
theorem solB : (-9 : ℤ) * ((584 : ℤ) ^ 3 - (14113 : ℤ) ^ 2) = 584 + 1 := by norm_num
/-- **Quantitative form of Problem 2 for (B).**  For every `k ≤ 9` the equation
`y (x³ - z²) = x + 1` has a solution with `min(|x|, |y|, |z|) ≥ k`. -/
theorem problem2B_le {k : ℤ} (hk : k ≤ 9) :
    ∃ x y z : ℤ, y * (x ^ 3 - z ^ 2) = x + 1 ∧ k ≤ |x| ∧ k ≤ |y| ∧ k ≤ |z| := by
  refine ⟨584, -9, 14113, solB, ?_, ?_, ?_⟩
  · rw [show |(584 : ℤ)| = 584 from by norm_num]; linarith
  · rw [show |(-9 : ℤ)| = 9 from by norm_num]; linarith
  · rw [show |(14113 : ℤ)| = 14113 from by norm_num]; linarith
end Table11
