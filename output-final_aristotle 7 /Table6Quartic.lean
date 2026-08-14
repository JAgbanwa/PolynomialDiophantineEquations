import RequestProject.FourthPowerValuation
/-!
# The equation `x⁴ + y⁴ + z³t - z t³ = 0`
This file studies the homogeneous quartic Diophantine equation
  `x⁴ + y⁴ + z³ t - z t³ = 0`,                                          (E)
which is one of the equations of size `H = 64` listed in Table 6 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*,
as an equation for which **Problem 3** is open.  Problem 3 asks whether a given
homogeneous equation has an integer solution in which *all* variables are
nonzero.
Equation (E) can be rewritten as
  `x⁴ + y⁴ = z t (t - z)(t + z)`,
i.e. a sum of two fourth powers equals the area of the (integral) right
triangle with legs `t² - z²` and `2 z t`.
## Main result
`Table6.no_solution_of_isCoprime`: **equation (E) has no integer solution with
`x` and `y` coprime.**  No nonvanishing hypothesis is needed: `x⁴ + y⁴ = 0`
forces `x = y = 0`, which is not coprime.
The proof is elementary and rests on two classical facts about a primitive sum
of two fourth powers `N = x⁴ + y⁴` with `gcd(x, y) = 1`, proved in
`RequestProject.SumFourthPowers`:
* every odd prime divisor of `N` is `≡ 1 (mod 8)`, hence every odd divisor of
  `N` is `≡ ±1 (mod 8)`;
* `N ≡ 1` or `2 (mod 16)`; in particular `4 ∤ N`.
Applied to the four factors `z`, `t`, `t - z`, `t + z` these force a
contradiction:
* if `z` and `t` are both even then `16 ∣ N`;
* if `z` and `t` are both odd then `8 ∣ N`;
* otherwise exactly one of `z`, `t` is even, hence `≡ 2 (mod 4)` (because
  `4 ∤ N`), while `t - z` and `t + z` are odd divisors of `N`, so both are
  `≡ ±1 (mod 8)`; but their difference `2z` (resp. their sum `2t`) is
  `≡ 4 (mod 8)`, which is impossible.
A second theorem, `Table6.no_solution_of_isCoprime_zt_of_not_both_even`, moves the coprimality
hypothesis to the other pair of variables: **(E) has no solution with `z` and `t`
coprime in which `x` and `y` are not both even.**  It uses the divisor results of
`RequestProject.FourthPowerValuation`, which do not require the sum of fourth
powers to be primitive.
This does **not** settle Problem 3 for (E): the equation is homogeneous, so a
hypothetical solution may only be normalised to have `gcd(x, y, z, t) = 1`, and
the arguments leave open the case where `gcd(x, y) > 1`, `gcd(z, t) > 1` and `x`,
`y` are both even.
-/
namespace Table6
open SumFourthPowers
/-- **Equation (E) has no integer solution with `x` and `y` coprime.**
In particular, `x⁴ + y⁴ + z³t - zt³ = 0` has no solution in nonzero integers with
`gcd(x, y) = 1`. -/
theorem no_solution_of_isCoprime (x y z t : ℤ) (hxy : IsCoprime x y)
    (h : x ^ 4 + y ^ 4 + z ^ 3 * t - z * t ^ 3 = 0) : False := by
  have hfact : x ^ 4 + y ^ 4 = z * t * (t - z) * (t + z) := by linear_combination h
  have hmod : (x ^ 4 + y ^ 4) % 16 = 1 ∨ (x ^ 4 + y ^ 4) % 16 = 2 :=
    sum_fourth_powers_mod_16 x y hxy
  have hzm : z % 2 = 0 ∨ z % 2 = 1 := by omega
  have htm : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hzm with hz | hz <;> rcases htm with ht | ht
  · -- both even: `16 ∣ N`
    obtain ⟨a, ha⟩ : ∃ a, z = 2 * a := ⟨z / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
    have hval : x ^ 4 + y ^ 4 = 16 * (a * b * (b - a) * (b + a)) := by
      rw [hfact, ha, hb]; ring
    omega
  · -- `z` even, `t` odd
    obtain ⟨a, ha⟩ : ∃ a, z = 2 * a := ⟨z / 2, by omega⟩
    have hNeven : x ^ 4 + y ^ 4 = 2 * (a * t * (t - z) * (t + z)) := by rw [hfact, ha]; ring
    have hN16 : (x ^ 4 + y ^ 4) % 16 = 2 := by omega
    -- `z ≡ 2 (mod 4)`
    have hz4 : z % 4 = 2 := by
      rcases (show z % 4 = 0 ∨ z % 4 = 2 by omega) with h4 | h4
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, z = 4 * c := ⟨z / 4, by omega⟩
        have : x ^ 4 + y ^ 4 = 4 * (c * t * (t - z) * (t + z)) := by
          rw [hfact]; rw [hc]; ring
        omega
      · exact h4
    have hd1 : (t - z) ∣ x ^ 4 + y ^ 4 := ⟨z * t * (t + z), by rw [hfact]; ring⟩
    have hd2 : (t + z) ∣ x ^ 4 + y ^ 4 := ⟨z * t * (t - z), by rw [hfact]; ring⟩
    have h1 := odd_dvd_mod_eight x y hxy (t - z) (by omega) hd1
    have h2 := odd_dvd_mod_eight x y hxy (t + z) (by omega) hd2
    omega
  · -- `z` odd, `t` even
    obtain ⟨b, hb⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
    have hNeven : x ^ 4 + y ^ 4 = 2 * (z * b * (t - z) * (t + z)) := by rw [hfact, hb]; ring
    have hN16 : (x ^ 4 + y ^ 4) % 16 = 2 := by omega
    have ht4 : t % 4 = 2 := by
      rcases (show t % 4 = 0 ∨ t % 4 = 2 by omega) with h4 | h4
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, t = 4 * c := ⟨t / 4, by omega⟩
        have : x ^ 4 + y ^ 4 = 4 * (z * c * (t - z) * (t + z)) := by
          rw [hfact]; rw [hc]; ring
        omega
      · exact h4
    have hd1 : (t - z) ∣ x ^ 4 + y ^ 4 := ⟨z * t * (t + z), by rw [hfact]; ring⟩
    have hd2 : (t + z) ∣ x ^ 4 + y ^ 4 := ⟨z * t * (t - z), by rw [hfact]; ring⟩
    have h1 := odd_dvd_mod_eight x y hxy (t - z) (by omega) hd1
    have h2 := odd_dvd_mod_eight x y hxy (t + z) (by omega) hd2
    omega
  · -- both odd: `8 ∣ N`
    obtain ⟨a, ha⟩ : ∃ a, z = 2 * a + 1 := ⟨z / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, t = 2 * b + 1 := ⟨t / 2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, (b - a) * (a + b + 1) = 2 * c := by
      rcases Int.even_or_odd (b - a) with ⟨d, hd⟩ | ⟨d, hd⟩
      · exact ⟨d * (a + b + 1), by rw [show b - a = d + d from hd]; ring⟩
      · refine ⟨(b - a) * (d + a + 1), ?_⟩
        have : a + b + 1 = 2 * (d + a + 1) := by omega
        rw [this]; ring
    have hval : x ^ 4 + y ^ 4 = 8 * ((2 * a + 1) * (2 * b + 1) * c) := by
      rw [hfact, ha, hb]
      linear_combination (4 * (2 * a + 1) * (2 * b + 1)) * hc
    omega
/-- **Equation (E) has no integer solution with `z` and `t` coprime in which `x` and `y` are
not both even.** -/
theorem no_solution_of_isCoprime_zt_of_not_both_even (x y z t : ℤ) (hzt : IsCoprime z t)
    (hxy : ¬ (x % 2 = 0 ∧ y % 2 = 0))
    (h : x ^ 4 + y ^ 4 + z ^ 3 * t - z * t ^ 3 = 0) : False := by
  have hfact : x ^ 4 + y ^ 4 = z * t * (t - z) * (t + z) := by linear_combination h
  have hmod : (x ^ 4 + y ^ 4) % 16 = 1 ∨ (x ^ 4 + y ^ 4) % 16 = 2 :=
    sum_fourth_powers_mod_16_of_not_both_even x y hxy
  have hne : x ^ 4 + y ^ 4 ≠ 0 := by omega
  -- `z` and `t` cannot both be odd, since then `4 ∣ x⁴ + y⁴`
  have hnotboth : ¬ (z % 2 = 1 ∧ t % 2 = 1) := by
    rintro ⟨hz, ht⟩
    obtain ⟨a, ha⟩ : ∃ a, z = 2 * a + 1 := ⟨z / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, t = 2 * b + 1 := ⟨t / 2, by omega⟩
    have hval : x ^ 4 + y ^ 4 = 4 * ((2 * a + 1) * (2 * b + 1) * ((b - a) * (a + b + 1))) := by
      rw [hfact, ha, hb]; ring
    omega
  -- exactly one of `z`, `t` is even; the argument is symmetric in the two cases
  have hmain : ∀ z t : ℤ, IsCoprime z t → z % 2 = 0 → t % 2 = 1 →
      x ^ 4 + y ^ 4 = z * t * (t - z) * (t + z) → False := by
    intro z t hzt hz ht hfact
    have hz4 : z % 4 = 2 := by
      rcases (show z % 4 = 0 ∨ z % 4 = 2 by omega) with h4 | h4
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, z = 4 * c := ⟨z / 4, by omega⟩
        have hval : x ^ 4 + y ^ 4 = 4 * (c * t * (t - z) * (t + z)) := by rw [hfact, hc]; ring
        omega
      · exact h4
    have hodd1 : (t - z) % 2 = 1 := by omega
    have hodd2 : (t + z) % 2 = 1 := by omega
    have hc1 : IsCoprime (t - z) z := by
      have h2 := hzt.add_mul_left_right (-1)
      rw [show t + z * (-1) = t - z by ring] at h2
      exact h2.symm
    have hc2 : IsCoprime (t - z) t := by
      have h1 : IsCoprime t (-z) := (hzt.symm).neg_right
      have h2 := h1.add_mul_left_right 1
      rw [show -z + t * 1 = t - z by ring] at h2
      exact h2.symm
    have hc3 : IsCoprime (t - z) (t + z) := by
      have h2 : IsCoprime (t - z) 2 :=
        ((Int.prime_two.coprime_iff_not_dvd).mpr (by omega)).symm
      have h4 : IsCoprime (t - z) (2 * z) := h2.mul_right hc1
      have h5 := h4.add_mul_left_right 1
      rw [show 2 * z + (t - z) * 1 = t + z by ring] at h5
      exact h5
    have hc4 : IsCoprime (t + z) z := by
      have h2 := hzt.add_mul_left_right 1
      rw [show t + z * 1 = t + z by ring] at h2
      exact h2.symm
    have hc5 : IsCoprime (t + z) t := by
      have h2 := (hzt.symm).add_mul_left_right 1
      rw [show z + t * 1 = t + z by ring] at h2
      exact h2.symm
    have hd1 := exact_divisor_mod_eight x y (t - z) (z * t * (t + z)) hne
      (by rw [hfact]; ring) ((hc1.mul_right hc2).mul_right hc3) hodd1
    have hd2 := exact_divisor_mod_eight x y (t + z) (z * t * (t - z)) hne
      (by rw [hfact]; ring) ((hc4.mul_right hc5).mul_right hc3.symm) hodd2
    omega
  rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz | hz
  · rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with ht | ht
    · exfalso
      have h2z : (2 : ℤ) ∣ z := by omega
      have h2t : (2 : ℤ) ∣ t := by omega
      have hu := hzt.isUnit_of_dvd' h2z h2t
      rw [Int.isUnit_iff] at hu
      omega
    · exact hmain z t hzt hz ht hfact
  · have ht : t % 2 = 0 := by
      by_contra hc
      exact hnotboth ⟨hz, by omega⟩
    -- replace `(z, t)` by `(t, -z)`, which leaves the right-hand side unchanged
    refine hmain t (-z) ((hzt.symm).neg_right) ht (by omega) ?_
    rw [hfact]; ring
end Table6
