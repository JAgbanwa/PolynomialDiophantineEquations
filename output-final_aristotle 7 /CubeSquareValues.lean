import RequestProject.PowerfulNumbers
/-!
# The open equations `x³y² = f(z)` and `x⁴y³ = f(z)`
B. Grechuk, *A systematic approach to Diophantine equations: open problems*, lists among
the shortest open equations several of the shape `x³y² = f(z)` or `x⁴y³ = f(z)`:
* Table 13 (**Problem 6**: does an integer solution exist?), lengths `l ≤ 10.6`:
  `x³y² = z⁴ + 2`, `x³y² = z⁴ − 3`, `x³y² = z³ + 6` (this last one is also equation (27),
  the smallest three-monomial equation for which Problem 6 is open) and `x⁴y³ = z² + 3`;
* Table 12 (**Problem 4**: list all integer solutions, or prove that there are infinitely
  many), length `l = 9`: `x³y² = z⁴ + 1`, `x³y² = z³ + 2`, `x³y² = 2z³ + 1` and
  `x⁴y³ = z² + 1`.
By `RequestProject.PowerfulNumbers`, `n` is of the form `x³y²` exactly when `n` is a
*powerful* number (no prime divides `n` exactly once), and of the form `x⁴y³` exactly
when no prime divides `n` once, twice or five times.  This turns each of these equations
into a one-variable question, and yields explicit congruence conditions that `z` must
satisfy.
## Main results
* `CubeSquare.exists_sol_cube_sq_iff` and `CubeSquare.exists_sol_pow4_cube_iff`: the four
  Problem-6 equations above have an integer solution **iff** the corresponding
  one-variable condition on `f(z)` holds for some `z` (stated separately for each
  equation as `CubeSquare.problem6_quartic_add_two_iff` etc.).
* Congruence obstructions, all unconditional:
  `z ≡ 1 (mod 2)` and `z mod 9 ∈ {0,2,3,6,7}` for `x³y² = z⁴ + 2`;
  `z` even and `3 ∤ z` for `x³y² = z⁴ − 3` and for `x⁴y³ = z² + 3`;
  `z` odd and `3 ∤ z` for `x³y² = z³ + 6`;
  `z` even for `x³y² = z⁴ + 1` and for `x⁴y³ = z² + 1`;
  `z` odd and `z ≢ 1 (mod 3)` for `x³y² = z³ + 2`;
  `z ≢ 1 (mod 3)` for `x³y² = 2z³ + 1`.
None of these equations is thereby resolved; the conditions are necessary, not
sufficient.
-/
namespace CubeSquare
open PowerfulNumbers
/-! ## Contradiction lemmas -/
/-- A prime cannot divide `x³y²` exactly once: the shape `4A + 2` is impossible. -/
theorem two_exact_cube_sq {x y A : ℤ} (h : x ^ 3 * y ^ 2 = 4 * A + 2) : False := by
  have h2 : (2 : ℤ) ∣ x ^ 3 * y ^ 2 := by rw [h]; exact ⟨2 * A + 1, by ring⟩
  have h4 := sq_dvd_of_prime_dvd Int.prime_two h2
  rw [h] at h4
  obtain ⟨k, hk⟩ := h4
  norm_num at hk
  omega
/-- The shape `9A + 3` or `9A + 6` is impossible for `x³y²`. -/
theorem three_exact_cube_sq {x y A c : ℤ} (hc : c = 3 ∨ c = 6)
    (h : x ^ 3 * y ^ 2 = 9 * A + c) : False := by
  have h3 : (3 : ℤ) ∣ x ^ 3 * y ^ 2 := by
    rw [h]
    rcases hc with rfl | rfl
    · exact ⟨3 * A + 1, by ring⟩
    · exact ⟨3 * A + 2, by ring⟩
  have h9 := sq_dvd_of_prime_dvd Int.prime_three h3
  rw [h] at h9
  obtain ⟨k, hk⟩ := h9
  norm_num at hk
  rcases hc with rfl | rfl <;> omega
/-- A prime cannot divide `x⁴y³` exactly once or twice: the shapes `8A + 2` and `8A + 4`
are impossible. -/
theorem two_exact_pow4_cube {x y A c : ℤ} (hc : c = 2 ∨ c = 4)
    (h : x ^ 4 * y ^ 3 = 8 * A + c) : False := by
  have h2 : (2 : ℤ) ∣ x ^ 4 * y ^ 3 := by
    rw [h]
    rcases hc with rfl | rfl
    · exact ⟨4 * A + 1, by ring⟩
    · exact ⟨4 * A + 2, by ring⟩
  have h8 := cube_dvd_of_prime_dvd Int.prime_two h2
  rw [h] at h8
  obtain ⟨k, hk⟩ := h8
  norm_num at hk
  rcases hc with rfl | rfl <;> omega
/-- The shape `9A + 3` or `9A + 6` is impossible for `x⁴y³`. -/
theorem three_exact_pow4_cube {x y A c : ℤ} (hc : c = 3 ∨ c = 6)
    (h : x ^ 4 * y ^ 3 = 9 * A + c) : False := by
  have h3 : (3 : ℤ) ∣ x ^ 4 * y ^ 3 := by
    rw [h]
    rcases hc with rfl | rfl
    · exact ⟨3 * A + 1, by ring⟩
    · exact ⟨3 * A + 2, by ring⟩
  have h27 := cube_dvd_of_prime_dvd Int.prime_three h3
  rw [h] at h27
  obtain ⟨k, hk⟩ := h27
  norm_num at hk
  rcases hc with rfl | rfl <;> omega
/-! ## `x³y² = z⁴ + 2`  (Table 13, Problem 6) -/
/-- In any solution of `x³y² = z⁴ + 2`, `z` is odd. -/
theorem quartic_add_two_odd {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 + 2) : z % 2 = 1 := by
  by_contra hodd
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  exact two_exact_cube_sq (A := 4 * w ^ 4) (by rw [h, hw]; ring)
/-- In any solution of `x³y² = z⁴ + 2`, `z` is congruent to `0, 2, 3, 6` or `7` mod `9`. -/
theorem quartic_add_two_mod_nine {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 + 2) :
    z % 9 = 0 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 6 ∨ z % 9 = 7 := by
  by_contra hcon
  have hr : z % 9 = 1 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 8 := by omega
  obtain ⟨q, hq⟩ : ∃ q, z = 9 * q + z % 9 := ⟨z / 9, by omega⟩
  rcases hr with hc | hc | hc | hc <;> rw [hc] at hq
  · exact three_exact_cube_sq (A := 729 * q ^ 4 + 324 * q ^ 3 + 54 * q ^ 2 + 4 * q) (c := 3)
      (Or.inl rfl) (by rw [h, hq]; ring)
  · exact three_exact_cube_sq
      (A := 729 * q ^ 4 + 1296 * q ^ 3 + 864 * q ^ 2 + 256 * q + 28) (c := 6)
      (Or.inr rfl) (by rw [h, hq]; ring)
  · exact three_exact_cube_sq
      (A := 729 * q ^ 4 + 1620 * q ^ 3 + 1350 * q ^ 2 + 500 * q + 69) (c := 6)
      (Or.inr rfl) (by rw [h, hq]; ring)
  · exact three_exact_cube_sq
      (A := 729 * q ^ 4 + 2592 * q ^ 3 + 3456 * q ^ 2 + 2048 * q + 455) (c := 3)
      (Or.inl rfl) (by rw [h, hq]; ring)
/-- **Problem 6 for `x³y² = z⁴ + 2`** is equivalent to the existence of an integer `z`
for which `z⁴ + 2` is a powerful number. -/
theorem problem6_quartic_add_two_iff :
    (∃ x y z : ℤ, x ^ 3 * y ^ 2 = z ^ 4 + 2) ↔
      ∃ z : ℤ, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ z ^ 4 + 2 → ((p : ℤ)) ^ 2 ∣ z ^ 4 + 2 := by
  have hne : ∀ z : ℤ, z ^ 4 + 2 ≠ 0 := fun z => by positivity
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨z, (exists_cube_mul_sq_iff (hne z)).mp ⟨x, y, h.symm⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := (exists_cube_mul_sq_iff (hne z)).mpr hz
    exact ⟨x, y, z, hxy.symm⟩
/-! ## `x³y² = z⁴ - 3`  (Table 13, Problem 6) -/
theorem quartic_sub_three_ne_zero (z : ℤ) : z ^ 4 - 3 ≠ 0 := by
  intro h
  rcases le_or_gt (z ^ 2) 1 with h1 | h1
  · nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  · nlinarith [sq_nonneg z]
/-- In any solution of `x³y² = z⁴ - 3`, `z` is even. -/
theorem quartic_sub_three_even {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 - 3) : z % 2 = 0 := by
  by_contra heven
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w + 1 := ⟨z / 2, by omega⟩
  exact two_exact_cube_sq (A := 4 * w ^ 4 + 8 * w ^ 3 + 6 * w ^ 2 + 2 * w - 1)
    (by rw [h, hw]; ring)
/-- In any solution of `x³y² = z⁴ - 3`, `z` is not divisible by `3`. -/
theorem quartic_sub_three_not_three_dvd {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 - 3) :
    z % 3 ≠ 0 := by
  intro h3
  obtain ⟨u, hu⟩ : ∃ u, z = 3 * u := ⟨z / 3, by omega⟩
  exact three_exact_cube_sq (A := 9 * u ^ 4 - 1) (c := 6) (Or.inr rfl) (by rw [h, hu]; ring)
/-- **Problem 6 for `x³y² = z⁴ - 3`** is equivalent to the existence of an integer `z`
for which `z⁴ - 3` is (up to sign) a powerful number. -/
theorem problem6_quartic_sub_three_iff :
    (∃ x y z : ℤ, x ^ 3 * y ^ 2 = z ^ 4 - 3) ↔
      ∃ z : ℤ, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ z ^ 4 - 3 → ((p : ℤ)) ^ 2 ∣ z ^ 4 - 3 := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨z, (exists_cube_mul_sq_iff (quartic_sub_three_ne_zero z)).mp ⟨x, y, h.symm⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := (exists_cube_mul_sq_iff (quartic_sub_three_ne_zero z)).mpr hz
    exact ⟨x, y, z, hxy.symm⟩
/-! ## `x³y² = z³ + 6`  (equation (27); Table 13, Problem 6) -/
theorem cubic_add_six_ne_zero (z : ℤ) : z ^ 3 + 6 ≠ 0 := by
  intro h
  rcases lt_trichotomy z (-1) with h1 | h1 | h1
  · have h2 : z ≤ -2 := by omega
    nlinarith [sq_nonneg (z + 2), sq_nonneg z]
  · subst h1; norm_num at h
  · nlinarith [sq_nonneg z]
/-- In any solution of `x³y² = z³ + 6`, `z` is odd. -/
theorem cubic_add_six_odd {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 3 + 6) : z % 2 = 1 := by
  by_contra hodd
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  exact two_exact_cube_sq (A := 2 * w ^ 3 + 1) (by rw [h, hw]; ring)
/-- In any solution of `x³y² = z³ + 6`, `z` is not divisible by `3`. -/
theorem cubic_add_six_not_three_dvd {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 3 + 6) :
    z % 3 ≠ 0 := by
  intro h3
  obtain ⟨u, hu⟩ : ∃ u, z = 3 * u := ⟨z / 3, by omega⟩
  exact three_exact_cube_sq (A := 3 * u ^ 3) (c := 6) (Or.inr rfl) (by rw [h, hu]; ring)
/-- **Problem 6 for `x³y² = z³ + 6`** — equation (27) of the paper, the smallest
three-monomial equation for which the existence of an integer solution is open — is
equivalent to the existence of an integer `z` for which `z³ + 6` is (up to sign) a
powerful number. -/
theorem problem6_cubic_add_six_iff :
    (∃ x y z : ℤ, x ^ 3 * y ^ 2 = z ^ 3 + 6) ↔
      ∃ z : ℤ, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ z ^ 3 + 6 → ((p : ℤ)) ^ 2 ∣ z ^ 3 + 6 := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨z, (exists_cube_mul_sq_iff (cubic_add_six_ne_zero z)).mp ⟨x, y, h.symm⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := (exists_cube_mul_sq_iff (cubic_add_six_ne_zero z)).mpr hz
    exact ⟨x, y, z, hxy.symm⟩
/-! ## `x⁴y³ = z² + 3`  (Table 13, Problem 6) -/
/-- In any solution of `x⁴y³ = z² + 3`, `z` is even. -/
theorem sq_add_three_even {x y z : ℤ} (h : x ^ 4 * y ^ 3 = z ^ 2 + 3) : z % 2 = 0 := by
  by_contra heven
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w + 1 := ⟨z / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, w ^ 2 + w = 2 * t := by
    obtain ⟨t, ht⟩ := Int.even_mul_succ_self w
    exact ⟨t, by linarith [ht]⟩
  refine two_exact_pow4_cube (x := x) (y := y) (A := t) (c := 4) (Or.inr rfl) ?_
  rw [h, hw]
  linear_combination 4 * ht
/-- In any solution of `x⁴y³ = z² + 3`, `z` is not divisible by `3`. -/
theorem sq_add_three_not_three_dvd {x y z : ℤ} (h : x ^ 4 * y ^ 3 = z ^ 2 + 3) :
    z % 3 ≠ 0 := by
  intro h3
  obtain ⟨u, hu⟩ : ∃ u, z = 3 * u := ⟨z / 3, by omega⟩
  exact three_exact_pow4_cube (A := u ^ 2) (c := 3) (Or.inl rfl) (by rw [h, hu]; ring)
/-- **Problem 6 for `x⁴y³ = z² + 3`** is equivalent to the existence of an integer `z`
such that no prime divides `z² + 3` exactly once, twice or five times. -/
theorem problem6_sq_add_three_iff :
    (∃ x y z : ℤ, x ^ 4 * y ^ 3 = z ^ 2 + 3) ↔
      ∃ z : ℤ, ∀ p : ℕ, p.Prime → (z ^ 2 + 3).natAbs.factorization p ≠ 1 ∧
        (z ^ 2 + 3).natAbs.factorization p ≠ 2 ∧
        (z ^ 2 + 3).natAbs.factorization p ≠ 5 := by
  have hne : ∀ z : ℤ, z ^ 2 + 3 ≠ 0 := fun z => by positivity
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨z, (exists_pow_four_mul_cube_iff (hne z)).mp ⟨x, y, h.symm⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := (exists_pow_four_mul_cube_iff (hne z)).mpr hz
    exact ⟨x, y, z, hxy.symm⟩
/-! ## Table 12 (Problem 4) -/
/-- In any solution of `x³y² = z⁴ + 1`, `z` is even. -/
theorem quartic_add_one_even {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 4 + 1) : z % 2 = 0 := by
  by_contra heven
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w + 1 := ⟨z / 2, by omega⟩
  exact two_exact_cube_sq (A := 4 * w ^ 4 + 8 * w ^ 3 + 6 * w ^ 2 + 2 * w)
    (by rw [h, hw]; ring)
/-- In any solution of `x⁴y³ = z² + 1`, `z` is even. -/
theorem sq_add_one_even {x y z : ℤ} (h : x ^ 4 * y ^ 3 = z ^ 2 + 1) : z % 2 = 0 := by
  by_contra heven
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w + 1 := ⟨z / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, w ^ 2 + w = 2 * t := by
    obtain ⟨t, ht⟩ := Int.even_mul_succ_self w
    exact ⟨t, by linarith [ht]⟩
  refine two_exact_pow4_cube (x := x) (y := y) (A := t) (c := 2) (Or.inl rfl) ?_
  rw [h, hw]
  linear_combination 4 * ht
/-- In any solution of `x³y² = z³ + 2`, `z` is odd. -/
theorem cubic_add_two_odd {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 3 + 2) : z % 2 = 1 := by
  by_contra hodd
  obtain ⟨w, hw⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  exact two_exact_cube_sq (A := 2 * w ^ 3) (by rw [h, hw]; ring)
/-- In any solution of `x³y² = z³ + 2`, `z` is not congruent to `1` mod `3`. -/
theorem cubic_add_two_mod_three {x y z : ℤ} (h : x ^ 3 * y ^ 2 = z ^ 3 + 2) : z % 3 ≠ 1 := by
  intro h3
  obtain ⟨u, hu⟩ : ∃ u, z = 3 * u + 1 := ⟨z / 3, by omega⟩
  exact three_exact_cube_sq (A := 3 * u ^ 3 + 3 * u ^ 2 + u) (c := 3) (Or.inl rfl)
    (by rw [h, hu]; ring)
/-- In any solution of `x³y² = 2z³ + 1`, `z` is not congruent to `1` mod `3`. -/
theorem two_cubic_add_one_mod_three {x y z : ℤ} (h : x ^ 3 * y ^ 2 = 2 * z ^ 3 + 1) :
    z % 3 ≠ 1 := by
  intro h3
  obtain ⟨u, hu⟩ : ∃ u, z = 3 * u + 1 := ⟨z / 3, by omega⟩
  exact three_exact_cube_sq (A := 6 * u ^ 3 + 6 * u ^ 2 + 2 * u) (c := 3) (Or.inl rfl)
    (by rw [h, hu]; ring)
end CubeSquare
