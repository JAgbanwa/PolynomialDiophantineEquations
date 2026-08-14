import RequestProject.FourthPowerValuation
/-!
# The equation `x⁴ + x y³ + z⁴ + t⁴ = 0`, second theorem
This file continues the study, begun in `RequestProject.Table6Quartic2`, of the
homogeneous quartic Diophantine equation
  `x⁴ + x y³ + z⁴ + t⁴ = 0`,                                            (F)
one of the equations of size `H = 64` listed in Table 6 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*,
as an equation for which **Problem 3** is open.
Whereas `Table6.no_solution_of_isCoprime_zt` assumes that `z` and `t` are
coprime, here the coprimality assumption is moved to the *other* pair of
variables.
## Main result
`Table6.no_solution_of_isCoprime_xy`: **equation (F) has no integer solution with
`x` and `y` coprime and `x (x + y) ≢ 0 (mod 16)`.**
Writing `V = z⁴ + t⁴`, `A = -x`, `B = x + y` and `C = x² - x y + y²`, equation
(F) says `V = A B C`, where `C = B² + 3AB + 3A²`.  Since `x` and `y` are
coprime, the factors `A`, `B`, `C` are pairwise coprime apart from a possible
common factor `3` between `B` and `C`.  By the results of
`RequestProject.FourthPowerValuation`, an odd factor of `V = z⁴ + t⁴` that is
coprime to its cofactor is `≡ ±1 (mod 8)` in absolute value, and `4 ∣ V` forces
`16 ∣ V`.  The hypothesis `16 ∤ x (x + y)` then pins down the `2`-adic
behaviour, and computing `C mod 8` from `C = B² + 3AB + 3A²` contradicts the
value forced by the divisor conditions in each of the three possible parity
cases.
Together with `Table6.no_solution_of_isCoprime_zt` this leaves Problem 3 for
(F) open only for solutions with `gcd(x, y) > 1`, `gcd(z, t) > 1` and
`16 ∣ x (x + y)`.
-/
namespace Table6
open SumFourthPowers
/-- If `4 ∣ m * n` and `n` is odd, then `4 ∣ m`. -/
theorem four_dvd_of_mul_odd (m n : ℤ) (hn : n % 2 = 1) (h : (4 : ℤ) ∣ m * n) : (4 : ℤ) ∣ m := by
  have hn2 : ¬ (2 : ℤ) ∣ n := by omega
  have hstep : ∀ k : ℤ, (2 : ℤ) ∣ k * n → (2 : ℤ) ∣ k := by
    intro k hk
    rcases Int.prime_two.dvd_mul.mp hk with h' | h'
    · exact h'
    · exact absurd h' hn2
  have hm2 : (2 : ℤ) ∣ m := hstep m (dvd_trans ⟨2, by norm_num⟩ h)
  obtain ⟨m', rfl⟩ := hm2
  obtain ⟨k, hk⟩ := h
  have h2 : (2 : ℤ) * (m' * n) = 2 * (2 * k) := by linear_combination hk
  have hm'n : m' * n = 2 * k := mul_left_cancel₀ two_ne_zero h2
  obtain ⟨m'', rfl⟩ := hstep m' ⟨k, hm'n⟩
  exact ⟨m'', by ring⟩
/-- The arithmetic core: there is no factorisation `z⁴ + t⁴ = A * B * C` with `A`, `B`
coprime, `C = B² + 3AB + 3A²` positive, and `16 ∤ A * B`. -/
theorem no_special_factorisation (z t A B C : ℤ)
    (heq : z ^ 4 + t ^ 4 = A * B * C) (hcop : IsCoprime A B)
    (hC : C = B ^ 2 + 3 * (A * B) + 3 * A ^ 2) (hCpos : 0 < C)
    (h16 : ¬ ((16 : ℤ) ∣ A * B)) : False := by
  have hA0 : A ≠ 0 := by rintro rfl; exact h16 (by simp)
  have hB0 : B ≠ 0 := by rintro rfl; exact h16 (by simp)
  have hVne : z ^ 4 + t ^ 4 ≠ 0 := by
    rw [heq]; exact mul_ne_zero (mul_ne_zero hA0 hB0) (ne_of_gt hCpos)
  have hVpos : 0 < z ^ 4 + t ^ 4 := lt_of_le_of_ne (by positivity) (Ne.symm hVne)
  have hABpos : 0 < A * B := by nlinarith [heq, hVpos, hCpos]
  -- `A` is coprime to `C`
  have hcopAC : IsCoprime A C := by
    have h1 : IsCoprime A (B ^ 2) := hcop.pow_right
    have h2 := h1.add_mul_left_right (3 * B + 3 * A)
    rwa [show B ^ 2 + A * (3 * B + 3 * A) = C by rw [hC]; ring] at h2
  have hcopA_BC : IsCoprime A (B * C) := hcop.mul_right hcopAC
  -- `A` and `B` are not both even
  have hnotboth : ¬ (A % 2 = 0 ∧ B % 2 = 0) := by
    rintro ⟨ha, hb⟩
    have h2A : (2 : ℤ) ∣ A := by omega
    have h2B : (2 : ℤ) ∣ B := by omega
    have hu := hcop.isUnit_of_dvd' h2A h2B
    rw [Int.isUnit_iff] at hu
    omega
  -- `C` is odd
  have hCodd : C % 2 = 1 := by
    rcases (show A % 2 = 0 ∨ A % 2 = 1 by omega) with ha | ha <;>
      rcases (show B % 2 = 0 ∨ B % 2 = 1 by omega) with hb | hb
    · exact absurd ⟨ha, hb⟩ hnotboth
    · obtain ⟨a, ha'⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
      obtain ⟨b, hb'⟩ : ∃ b, B = 2 * b + 1 := ⟨B / 2, by omega⟩
      have hexp : C = 2 * (2 * b ^ 2 + 2 * b + 6 * a * b + 3 * a + 6 * a ^ 2) + 1 := by
        rw [hC, ha', hb']; ring
      omega
    · obtain ⟨a, ha'⟩ : ∃ a, A = 2 * a + 1 := ⟨A / 2, by omega⟩
      obtain ⟨b, hb'⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
      have hexp : C = 2 * (2 * b ^ 2 + 6 * a * b + 3 * b + 6 * a ^ 2 + 6 * a + 1) + 1 := by
        rw [hC, ha', hb']; ring
      omega
    · obtain ⟨a, ha'⟩ : ∃ a, A = 2 * a + 1 := ⟨A / 2, by omega⟩
      obtain ⟨b, hb'⟩ : ∃ b, B = 2 * b + 1 := ⟨B / 2, by omega⟩
      have hexp : C = 2 * (6 * a ^ 2 + 6 * a * b + 2 * b ^ 2 + 9 * a + 5 * b + 3) + 1 := by
        rw [hC, ha', hb']; ring
      omega
  -- `C ≡ 1` or `3 (mod 8)`
  have hCmod : C % 8 = 1 ∨ C % 8 = 3 := by
    by_cases h3 : (3 : ℤ) ∣ C
    · -- then `3 ∣ B`, `3 ∤ A`, and `C = 3 * C₂` with `C₂` an exact divisor of `V`
      have h3B2 : (3 : ℤ) ∣ B ^ 2 := by
        obtain ⟨k, hk⟩ := h3
        exact ⟨k - A * B - A ^ 2, by rw [hC] at hk; linear_combination hk⟩
      have h3B : (3 : ℤ) ∣ B := Int.Prime.dvd_pow' (p := 3) (by norm_num) h3B2
      obtain ⟨B', rfl⟩ := h3B
      have h3A : ¬ (3 : ℤ) ∣ A := by
        intro hd
        have hu := hcop.isUnit_of_dvd' hd ⟨B', rfl⟩
        rw [Int.isUnit_iff] at hu
        omega
      set C₂ : ℤ := 3 * B' ^ 2 + 3 * A * B' + A ^ 2 with hC₂def
      have hCC : C = 3 * C₂ := by rw [hC, hC₂def]; ring
      have h3C₂ : ¬ (3 : ℤ) ∣ C₂ := by
        intro hd
        refine h3A (Int.Prime.dvd_pow' (p := 3) (n := A) (k := 2) (by norm_num) ?_)
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - B' ^ 2 - A * B', by rw [hC₂def] at hk; linear_combination hk⟩
      have hcopAB' : IsCoprime A B' := hcop.of_isCoprime_of_dvd_right ⟨3, by ring⟩
      have hcopC₂3 : IsCoprime C₂ 3 := ((Int.prime_three.coprime_iff_not_dvd).mpr h3C₂).symm
      have hcopC₂A : IsCoprime C₂ A := by
        have h1 : IsCoprime A 3 := ((Int.prime_three.coprime_iff_not_dvd).mpr h3A).symm
        have h2 : IsCoprime A (B' ^ 2) := hcopAB'.pow_right
        have h3' : IsCoprime A (3 * B' ^ 2) := h1.mul_right h2
        have h4 := h3'.add_mul_left_right (A + 3 * B')
        rw [show 3 * B' ^ 2 + A * (A + 3 * B') = C₂ by rw [hC₂def]; ring] at h4
        exact h4.symm
      have hcopC₂B' : IsCoprime C₂ B' := by
        have h1 : IsCoprime B' (A ^ 2) := (hcopAB'.symm).pow_right
        have h2 := h1.add_mul_left_right (3 * B' + 3 * A)
        rw [show A ^ 2 + B' * (3 * B' + 3 * A) = C₂ by rw [hC₂def]; ring] at h2
        exact h2.symm
      have hcopC₂ : IsCoprime C₂ (9 * A * B') :=
        ((hcopC₂3.mul_right hcopC₂3).mul_right hcopC₂A).mul_right hcopC₂B'
      have hC₂odd : C₂ % 2 = 1 := by omega
      have hC₂pos : 0 < C₂ := by omega
      have hdiv := exact_divisor_mod_eight z t C₂ (9 * A * B') hVne
        (by rw [heq, hCC]; ring) hcopC₂ hC₂odd
      omega
    · -- `C` is coprime to `A * B`
      have h3B : ¬ (3 : ℤ) ∣ B := by
        intro hd
        refine h3 ?_
        obtain ⟨k, hk⟩ := hd
        exact ⟨k * B + A * B + A ^ 2, by rw [hC, hk]; ring⟩
      have hcopCB : IsCoprime C B := by
        have h1 : IsCoprime B 3 := ((Int.prime_three.coprime_iff_not_dvd).mpr h3B).symm
        have h2 : IsCoprime B (A ^ 2) := (hcop.symm).pow_right
        have h3' : IsCoprime B (3 * A ^ 2) := h1.mul_right h2
        have h4 := h3'.add_mul_left_right (B + 3 * A)
        rw [show 3 * A ^ 2 + B * (B + 3 * A) = C by rw [hC]; ring] at h4
        exact h4.symm
      have hcopC : IsCoprime C (A * B) := hcopAC.symm.mul_right hcopCB
      have hdiv := exact_divisor_mod_eight z t C (A * B) hVne (by rw [heq]; ring) hcopC hCodd
      omega
  -- parity case analysis
  rcases (show A % 2 = 0 ∨ A % 2 = 1 by omega) with ha | ha <;>
    rcases (show B % 2 = 0 ∨ B % 2 = 1 by omega) with hb | hb
  · exact absurd ⟨ha, hb⟩ hnotboth
  · -- `A` even, `B` odd
    have hA4 : ¬ (4 : ℤ) ∣ A := by
      intro hd
      have h4V : (4 : ℤ) ∣ z ^ 4 + t ^ 4 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k * B * C, by rw [heq, hk]; ring⟩
      have h16V : (16 : ℤ) ∣ z ^ 4 + t ^ 4 := four_dvd_or_sixteen_dvd z t h4V
      obtain ⟨a, ha'⟩ := hd
      obtain ⟨k, hk⟩ := h16V
      have hstep : (4 : ℤ) ∣ a * (B * C) := by
        refine ⟨k, ?_⟩
        have h2 : (4 : ℤ) * (a * (B * C)) = 4 * (4 * k) := by
          rw [heq] at hk; linear_combination hk - B * C * ha'
        exact mul_left_cancel₀ (by norm_num) h2
      have hBCodd : (B * C) % 2 = 1 := by
        have hm := Int.mul_emod B C 2
        rw [hb, hCodd] at hm
        simpa using hm
      have h4a : (4 : ℤ) ∣ a := four_dvd_of_mul_odd a (B * C) hBCodd hstep
      obtain ⟨a', ha''⟩ := h4a
      exact h16 ⟨a' * B, by rw [ha', ha'']; ring⟩
    obtain ⟨A₁, hA₁⟩ : ∃ A₁, A = 2 * A₁ := ⟨A / 2, by omega⟩
    have hA₁odd : A₁ % 2 = 1 := by omega
    have hcopA₁ : IsCoprime A₁ (2 * (B * C)) := by
      have h2 : IsCoprime A₁ 2 := ((Int.prime_two.coprime_iff_not_dvd).mpr (by omega)).symm
      have hAA₁ : A₁ ∣ A := ⟨2, by rw [hA₁]; ring⟩
      exact h2.mul_right (hcopA_BC.of_isCoprime_of_dvd_left hAA₁)
    have hdivA := exact_divisor_mod_eight z t A₁ (2 * (B * C)) hVne
      (by rw [heq, hA₁]; ring) hcopA₁ hA₁odd
    have hBCodd : (B * C) % 2 = 1 := by
      have hm := Int.mul_emod B C 2
      rw [hb, hCodd] at hm
      simpa using hm
    have hdivBC := exact_divisor_mod_eight z t (B * C) A hVne (by rw [heq]; ring)
      hcopA_BC.symm hBCodd
    -- numerics
    have hA₁Bpos : 0 < A₁ * B := by
      have : A * B = 2 * (A₁ * B) := by rw [hA₁]; ring
      omega
    have hnA₁B : (A₁ * B).natAbs = A₁.natAbs * B.natAbs := Int.natAbs_mul _ _
    have hnBC : (B * C).natAbs = B.natAbs * C.natAbs := Int.natAbs_mul _ _
    have hCnat : C.natAbs % 8 = C % 8 % 8 := by omega
    have hr : B.natAbs % 8 = C.natAbs % 8 := by
      have hmul := Nat.mul_mod B.natAbs C.natAbs 8
      have hb8 : B.natAbs % 8 < 8 := Nat.mod_lt _ (by norm_num)
      have hc8 : C.natAbs % 8 = 1 ∨ C.natAbs % 8 = 3 := by omega
      rw [hnBC] at hdivBC
      rcases hc8 with hc | hc <;> rw [hc] at hmul <;> omega
    have hABmod : (A₁ * B) % 8 = C % 8 := by
      have hmul := Nat.mul_mod A₁.natAbs B.natAbs 8
      rw [hdivA] at hmul
      omega
    have hA₁sq : A₁ ^ 2 % 8 = 1 := odd_sq_mod_eight A₁ hA₁odd
    have hBsq : B ^ 2 % 8 = 1 := odd_sq_mod_eight B hb
    have hCexp : C = B ^ 2 + 6 * (A₁ * B) + 12 * A₁ ^ 2 := by rw [hC, hA₁]; ring
    omega
  · -- `A` odd, `B` even
    have hB4 : ¬ (4 : ℤ) ∣ B := by
      intro hd
      have h4V : (4 : ℤ) ∣ z ^ 4 + t ^ 4 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨A * k * C, by rw [heq, hk]; ring⟩
      have h16V : (16 : ℤ) ∣ z ^ 4 + t ^ 4 := four_dvd_or_sixteen_dvd z t h4V
      obtain ⟨b, hb'⟩ := hd
      obtain ⟨k, hk⟩ := h16V
      have hstep : (4 : ℤ) ∣ b * (A * C) := by
        refine ⟨k, ?_⟩
        have h2 : (4 : ℤ) * (b * (A * C)) = 4 * (4 * k) := by
          rw [heq] at hk; linear_combination hk - A * C * hb'
        exact mul_left_cancel₀ (by norm_num) h2
      have hACodd : (A * C) % 2 = 1 := by
        have hm := Int.mul_emod A C 2
        rw [ha, hCodd] at hm
        simpa using hm
      have h4b : (4 : ℤ) ∣ b := four_dvd_of_mul_odd b (A * C) hACodd hstep
      obtain ⟨b', hb''⟩ := h4b
      exact h16 ⟨A * b', by rw [hb', hb'']; ring⟩
    obtain ⟨B₁, hB₁⟩ : ∃ B₁, B = 2 * B₁ := ⟨B / 2, by omega⟩
    have hB₁odd : B₁ % 2 = 1 := by omega
    have hcopB₁C : IsCoprime (B₁ * C) (2 * A) := by
      have h2 : IsCoprime (B₁ * C) 2 := by
        refine ((Int.prime_two.coprime_iff_not_dvd).mpr ?_).symm
        have hm := Int.mul_emod B₁ C 2
        rw [hB₁odd, hCodd] at hm
        omega
      have hB₁A : IsCoprime B₁ A := (hcop.symm).of_isCoprime_of_dvd_left ⟨2, by rw [hB₁]; ring⟩
      exact h2.mul_right (hB₁A.mul_left hcopAC.symm)
    have hB₁Codd : (B₁ * C) % 2 = 1 := by
      have hm := Int.mul_emod B₁ C 2
      rw [hB₁odd, hCodd] at hm
      simpa using hm
    have hdivBC := exact_divisor_mod_eight z t (B₁ * C) (2 * A) hVne
      (by rw [heq, hB₁]; ring) hcopB₁C hB₁Codd
    have hdivA := exact_divisor_mod_eight z t A (B * C) hVne (by rw [heq]; ring) hcopA_BC ha
    have hAB₁pos : 0 < A * B₁ := by
      have : A * B = 2 * (A * B₁) := by rw [hB₁]; ring
      omega
    have hnAB₁ : (A * B₁).natAbs = A.natAbs * B₁.natAbs := Int.natAbs_mul _ _
    have hnB₁C : (B₁ * C).natAbs = B₁.natAbs * C.natAbs := Int.natAbs_mul _ _
    have hr : B₁.natAbs % 8 = C.natAbs % 8 := by
      have hmul := Nat.mul_mod B₁.natAbs C.natAbs 8
      have hc8 : C.natAbs % 8 = 1 ∨ C.natAbs % 8 = 3 := by omega
      rw [hnB₁C] at hdivBC
      rcases hc8 with hc | hc <;> rw [hc] at hmul <;> omega
    have hABmod : (A * B₁) % 8 = C % 8 := by
      have hmul := Nat.mul_mod A.natAbs B₁.natAbs 8
      rw [hdivA] at hmul
      omega
    have hAsq : A ^ 2 % 8 = 1 := odd_sq_mod_eight A ha
    have hB₁sq : B₁ ^ 2 % 8 = 1 := odd_sq_mod_eight B₁ hB₁odd
    have hCexp : C = 4 * B₁ ^ 2 + 6 * (A * B₁) + 3 * A ^ 2 := by rw [hC, hB₁]; ring
    omega
  · -- `A` and `B` both odd
    have hdivA := exact_divisor_mod_eight z t A (B * C) hVne (by rw [heq]; ring) hcopA_BC ha
    have hBCodd : (B * C) % 2 = 1 := by
      have hm := Int.mul_emod B C 2
      rw [hb, hCodd] at hm
      simpa using hm
    have hdivBC := exact_divisor_mod_eight z t (B * C) A hVne (by rw [heq]; ring)
      hcopA_BC.symm hBCodd
    have hnAB : (A * B).natAbs = A.natAbs * B.natAbs := Int.natAbs_mul _ _
    have hnBC : (B * C).natAbs = B.natAbs * C.natAbs := Int.natAbs_mul _ _
    have hr : B.natAbs % 8 = C.natAbs % 8 := by
      have hmul := Nat.mul_mod B.natAbs C.natAbs 8
      have hc8 : C.natAbs % 8 = 1 ∨ C.natAbs % 8 = 3 := by omega
      rw [hnBC] at hdivBC
      rcases hc8 with hc | hc <;> rw [hc] at hmul <;> omega
    have hABmod : (A * B) % 8 = C % 8 := by
      have hmul := Nat.mul_mod A.natAbs B.natAbs 8
      rw [hdivA] at hmul
      omega
    have hAsq : A ^ 2 % 8 = 1 := odd_sq_mod_eight A ha
    have hBsq : B ^ 2 % 8 = 1 := odd_sq_mod_eight B hb
    omega
/-- Equation (F) has no integer solution with `x`, `y` coprime and `16 ∤ x (x + y)`. -/
theorem no_solution_of_isCoprime_xy (x y z t : ℤ) (hxy : IsCoprime x y)
    (h16 : ¬ ((16 : ℤ) ∣ x * (x + y)))
    (h : x ^ 4 + x * y ^ 3 + z ^ 4 + t ^ 4 = 0) : False := by
  have hx0 : x ≠ 0 := by rintro rfl; exact h16 (by simp)
  have hcop : IsCoprime (-x) (x + y) := by
    have h1 : IsCoprime (-x) y := hxy.neg_left
    have h2 := h1.add_mul_left_right (-1)
    rwa [show y + -x * -1 = x + y by ring] at h2
  have hCpos : 0 < x ^ 2 - x * y + y ^ 2 := by
    rcases eq_or_ne y 0 with rfl | hy
    · have hx2 : 0 < x ^ 2 := pow_two_pos_of_ne_zero hx0
      nlinarith
    · have hy2 : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy
      nlinarith [sq_nonneg (2 * x - y)]
  refine no_special_factorisation z t (-x) (x + y) (x ^ 2 - x * y + y ^ 2)
    (by linear_combination h) hcop (by ring) hCpos ?_
  intro hd
  exact h16 (by
    obtain ⟨k, hk⟩ := hd
    exact ⟨-k, by linarith [hk]⟩)
/-- **Equation (F) has no integer solution with `x` and `y` coprime in which `z` and `t` are
not both even.**
This is the form in which the hypothesis is most natural: for a solution with `gcd(x, y) = 1`
the condition `16 ∤ x (x + y)` of `Table6.no_solution_of_isCoprime_xy` is equivalent to `z`
and `t` not being both even. -/
theorem no_solution_of_isCoprime_xy_of_not_both_even (x y z t : ℤ) (hxy : IsCoprime x y)
    (hzt : ¬ ((2 : ℤ) ∣ z ∧ (2 : ℤ) ∣ t))
    (h : x ^ 4 + x * y ^ 3 + z ^ 4 + t ^ 4 = 0) : False := by
  refine no_solution_of_isCoprime_xy x y z t hxy ?_ h
  intro hd
  -- `16 ∣ x (x + y)` would force `16 ∣ z⁴ + t⁴`, hence `z` and `t` both even
  have hV : (16 : ℤ) ∣ z ^ 4 + t ^ 4 := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨-(k * (x ^ 2 - x * y + y ^ 2)), ?_⟩
    linear_combination h - (x ^ 2 - x * y + y ^ 2) * hk
  refine hzt ?_
  rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz | hz <;>
    rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with ht | ht
  · exact ⟨by omega, by omega⟩
  · exfalso
    have h1 := even_fourth_pow_mod_sixteen z hz
    have h2 := odd_fourth_pow_mod_sixteen t ht
    omega
  · exfalso
    have h1 := odd_fourth_pow_mod_sixteen z hz
    have h2 := even_fourth_pow_mod_sixteen t ht
    omega
  · exfalso
    have h1 := odd_fourth_pow_mod_sixteen z hz
    have h2 := odd_fourth_pow_mod_sixteen t ht
    omega
end Table6
