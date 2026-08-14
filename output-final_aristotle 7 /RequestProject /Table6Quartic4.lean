/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib
/-!
# Table 6 (Problem 3): the equation `x⁴ + x³y + xy³ − z⁴ = 0`
Problem 3 of B. Grechuk, *A systematic approach to Diophantine equations: open problems*
asks, for a homogeneous polynomial `P`, whether `P = 0` has an integer solution in which
**all** variables are nonzero.  The equation
```
x⁴ + x³y + xy³ − z⁴ = 0                                        (G)      (H = 64)
```
is one of the five equations of Table 6 for which this question is open.  This file
collects what can be proved about (G) by elementary means.  All statements are
unconditional: no solution is assumed to be primitive.
Main results:
* `Table6.quarticG_not_both_odd` — (G) has no solution with `x` and `y` both odd
  (a congruence mod `4`);
* `Table6.quarticG_sixteen_dvd_y_of_odd_x`, `Table6.quarticG_sixteen_dvd_x_of_odd_y` —
  if one of `x`, `y` is odd, then `16` divides the other one;
* `Table6.quarticG_sixteen_dvd_of_not_both_even` — consequently, in every solution in
  which `x` and `y` are not both even, `16 ∣ x` or `16 ∣ y`;
* `Table6.quarticG_descent_two` — if `x` and `y` are both even, then `z` is even and
  `(x/2, y/2, z/2)` is again a solution, so the hypothesis "`x`, `y` not both even" is
  no restriction;
* `Table6.quarticG_exists_coprime_solution` — every solution with `x`, `y`, `z` nonzero
  gives rise to one with `x`, `y`, `z` nonzero and `gcd(x, y) = 1`; hence Problem 3 for
  (G) is equivalent to its coprime case;
* `Table6.quarticG_fourth_powers_of_isCoprime` — in a coprime solution with `x ≠ 0` and
  `z ≠ 0`, the two coprime factors `x` and `x³ + x²y + y³` of `z⁴` are, up to a common
  sign, perfect fourth powers.
-/
namespace Table6
/-! ### The underlying congruences -/
private theorem zmod4_odd_odd : ∀ U V Z : ZMod 4,
    (2 * U + 1) ^ 4 + (2 * U + 1) ^ 3 * (2 * V + 1) + (2 * U + 1) * (2 * V + 1) ^ 3 ≠ Z ^ 4 := by
  decide
private theorem zmod16_odd_left : ∀ U Y Z : ZMod 16,
    (2 * U + 1) ^ 4 + (2 * U + 1) ^ 3 * Y + (2 * U + 1) * Y ^ 3 = Z ^ 4 → Y = 0 := by
  decide
private theorem zmod16_odd_right : ∀ X V Z : ZMod 16,
    X ^ 4 + X ^ 3 * (2 * V + 1) + X * (2 * V + 1) ^ 3 = Z ^ 4 → X = 0 := by
  decide
/-- **(G) has no solution with `x` and `y` both odd.**
Indeed `x⁴ + x³y + xy³ ≡ 3 (mod 4)` for odd `x`, `y`, whereas a fourth power is `0` or
`1` mod `4`. -/
theorem quarticG_not_both_odd {x y z : ℤ} (hx : Odd x) (hy : Odd y) :
    x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  intro h
  have h' : (2 * u + 1) ^ 4 + (2 * u + 1) ^ 3 * (2 * v + 1) + (2 * u + 1) * (2 * v + 1) ^ 3
      = z ^ 4 := by linarith
  have hc := congrArg (fun n : ℤ => (n : ZMod 4)) h'
  push_cast at hc
  exact zmod4_odd_odd _ _ _ hc
/-- If `x` is odd, then `16 ∣ y` in every solution of (G). -/
theorem quarticG_sixteen_dvd_y_of_odd_x {x y z : ℤ} (hx : Odd x)
    (h : x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 = 0) : (16 : ℤ) ∣ y := by
  obtain ⟨u, rfl⟩ := hx
  have h' : (2 * u + 1) ^ 4 + (2 * u + 1) ^ 3 * y + (2 * u + 1) * y ^ 3 = z ^ 4 := by linarith
  have hc := congrArg (fun n : ℤ => (n : ZMod 16)) h'
  push_cast at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd y 16).mp (zmod16_odd_left _ _ _ hc)
/-- If `y` is odd, then `16 ∣ x` in every solution of (G). -/
theorem quarticG_sixteen_dvd_x_of_odd_y {x y z : ℤ} (hy : Odd y)
    (h : x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 = 0) : (16 : ℤ) ∣ x := by
  obtain ⟨v, rfl⟩ := hy
  have h' : x ^ 4 + x ^ 3 * (2 * v + 1) + x * (2 * v + 1) ^ 3 = z ^ 4 := by linarith
  have hc := congrArg (fun n : ℤ => (n : ZMod 16)) h'
  push_cast at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 16).mp (zmod16_odd_right _ _ _ hc)
/-- **In every solution of (G) in which `x` and `y` are not both even, `16` divides one of
them.**  (They cannot both be odd, by `quarticG_not_both_odd`.) -/
theorem quarticG_sixteen_dvd_of_not_both_even {x y z : ℤ}
    (hnot : ¬ ((2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y))
    (h : x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 = 0) : (16 : ℤ) ∣ x ∨ (16 : ℤ) ∣ y := by
  rcases Int.even_or_odd x with hx | hx
  · have hy : Odd y := by
      rcases Int.even_or_odd y with hy | hy
      · exact absurd ⟨hx.two_dvd, hy.two_dvd⟩ hnot
      · exact hy
    exact Or.inl (quarticG_sixteen_dvd_x_of_odd_y hy h)
  · exact Or.inr (quarticG_sixteen_dvd_y_of_odd_x hx h)
/-! ### Descent -/
/-- If a prime `p` divides both `x` and `y` in a solution of (G), then it divides `z`
as well, and dividing all three variables by `p` again gives a solution of (G). -/
theorem quarticG_descent_prime {p x y z : ℤ} (hp : Prime p)
    (h : (p * x) ^ 4 + (p * x) ^ 3 * (p * y) + (p * x) * (p * y) ^ 3 - z ^ 4 = 0) :
    ∃ w : ℤ, z = p * w ∧ x ^ 4 + x ^ 3 * y + x * y ^ 3 - w ^ 4 = 0 := by
  have hz4 : z ^ 4 = p ^ 4 * (x ^ 4 + x ^ 3 * y + x * y ^ 3) := by ring_nf; ring_nf at h; linarith
  have hpz : p ∣ z := by
    have : p ∣ z ^ 4 := ⟨p ^ 3 * (x ^ 4 + x ^ 3 * y + x * y ^ 3), by rw [hz4]; ring⟩
    exact hp.dvd_of_dvd_pow this
  obtain ⟨w, rfl⟩ := hpz
  refine ⟨w, rfl, ?_⟩
  have h4 : p ^ 4 * w ^ 4 = p ^ 4 * (x ^ 4 + x ^ 3 * y + x * y ^ 3) := by rw [← hz4]; ring
  have := mul_left_cancel₀ (pow_ne_zero 4 hp.ne_zero) h4
  linarith
/-- If `x` and `y` are both even in a solution of (G), then so is `z`, and halving all
three variables again gives a solution of (G). -/
theorem quarticG_descent_two {x y z : ℤ}
    (h : (2 * x) ^ 4 + (2 * x) ^ 3 * (2 * y) + (2 * x) * (2 * y) ^ 3 - z ^ 4 = 0) :
    ∃ w : ℤ, z = 2 * w ∧ x ^ 4 + x ^ 3 * y + x * y ^ 3 - w ^ 4 = 0 :=
  quarticG_descent_prime Int.prime_two h
/-- **Reduction of Problem 3 for (G) to the coprime case.**
If (G) has a solution with all variables nonzero, then it has one with all variables
nonzero in which moreover `x` and `y` are coprime. -/
theorem quarticG_exists_coprime_solution {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 = 0) :
    ∃ X Y Z : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧ IsCoprime X Y ∧
      X ^ 4 + X ^ 3 * Y + X * Y ^ 3 - Z ^ 4 = 0 := by
  induction hn : x.natAbs using Nat.strong_induction_on generalizing x y z with
  | _ n ih =>
    by_cases hco : IsCoprime x y
    · exact ⟨x, y, z, hx, hy, hz, hco, h⟩
    · have hg : Int.gcd x y ≠ 1 := fun hg => hco (Int.isCoprime_iff_gcd_eq_one.mpr hg)
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
      have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hpg : ((p : ℤ)) ∣ (Int.gcd x y : ℤ) := Int.natCast_dvd_natCast.mpr hpd
      have hpx : ((p : ℤ)) ∣ x := hpg.trans (Int.gcd_dvd_left x y)
      have hpy : ((p : ℤ)) ∣ y := hpg.trans (Int.gcd_dvd_right x y)
      obtain ⟨X, rfl⟩ := hpx
      obtain ⟨Y, rfl⟩ := hpy
      obtain ⟨w, rfl, hnew⟩ := quarticG_descent_prime hpi h
      have hX : X ≠ 0 := by rintro rfl; simp at hx
      have hY : Y ≠ 0 := by rintro rfl; simp at hy
      have hw : w ≠ 0 := by rintro rfl; simp at hz
      have hlt : X.natAbs < n := by
        have hXpos : 0 < X.natAbs := Int.natAbs_pos.mpr hX
        have h2 : 2 ≤ p := hp.two_le
        have hne : n = p * X.natAbs := by rw [← hn]; simp [Int.natAbs_mul]
        rw [hne]; nlinarith
      exact ih X.natAbs hlt hX hY hw hnew rfl
/-! ### The fourth-power factorisation in the coprime case -/
/-- If `a` and `b` are coprime integers whose product is a fourth power, then `a` is
`± a fourth power`. -/
theorem pm_fourth_power_of_isCoprime {a b c : ℤ} (h : IsCoprime a b) (hab : a * b = c ^ 4) :
    ∃ d : ℤ, a = d ^ 4 ∨ a = -d ^ 4 := by
  have hu : IsUnit (gcd a b) := by
    rw [Int.isCoprime_iff_gcd_eq_one] at h
    have : gcd a b = 1 := by rw [← Int.coe_gcd, h]; rfl
    simp [this]
  obtain ⟨d, u, hu2⟩ := exists_associated_pow_of_mul_eq_pow hu hab
  rcases Int.isUnit_iff.mp u.isUnit with h1 | h1 <;>
    · refine ⟨d, ?_⟩
      rw [← hu2, h1]
      simp
/-- **The fourth-power factorisation of a coprime solution of (G).**
Writing (G) as `x · (x³ + x²y + y³) = z⁴`, the two factors are coprime, hence each of
them is a fourth power up to a common sign. -/
theorem quarticG_fourth_powers_of_isCoprime {x y z : ℤ} (hx : x ≠ 0) (hz : z ≠ 0)
    (hco : IsCoprime x y) (h : x ^ 4 + x ^ 3 * y + x * y ^ 3 - z ^ 4 = 0) :
    ∃ a b : ℤ, (x = a ^ 4 ∧ x ^ 3 + x ^ 2 * y + y ^ 3 = b ^ 4) ∨
      (x = -a ^ 4 ∧ x ^ 3 + x ^ 2 * y + y ^ 3 = -b ^ 4) := by
  set X : ℤ := x ^ 3 + x ^ 2 * y + y ^ 3 with hXdef
  have hprod : x * X = z ^ 4 := by rw [hXdef]; linarith [h]
  have hcoX : IsCoprime x X := by
    have h3 : IsCoprime x (y ^ 3) := (hco.pow_right : IsCoprime x (y ^ 3))
    have : IsCoprime x (y ^ 3 + x * (x ^ 2 + x * y)) := h3.add_mul_left_right _
    have heq : y ^ 3 + x * (x ^ 2 + x * y) = X := by rw [hXdef]; ring
    rwa [heq] at this
  obtain ⟨a, ha⟩ := pm_fourth_power_of_isCoprime hcoX hprod
  obtain ⟨b, hb⟩ := pm_fourth_power_of_isCoprime hcoX.symm (by rw [mul_comm]; exact hprod)
  have hz4 : 0 < z ^ 4 := by positivity
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact absurd hprod.symm (ne_of_gt hz4)
  rcases ha with ha | ha
  · -- `x = a⁴ > 0`, hence `X > 0`
    have ha4 : (0:ℤ) ≤ a ^ 4 := by positivity
    have hxpos : 0 < x := lt_of_le_of_ne (ha ▸ ha4) (Ne.symm hx)
    have hXpos : 0 < X := by nlinarith [hprod, hz4]
    refine ⟨a, b, Or.inl ⟨ha, ?_⟩⟩
    rcases hb with hb | hb
    · exact hb
    · exfalso
      have hb4 : (0:ℤ) ≤ b ^ 4 := by positivity
      linarith [hb ▸ hXpos]
  · have ha4 : (0:ℤ) ≤ a ^ 4 := by positivity
    have hxneg : x < 0 := lt_of_le_of_ne (by linarith [ha]) hx
    have hXneg : X < 0 := by nlinarith [hprod, hz4]
    refine ⟨a, b, Or.inr ⟨ha, ?_⟩⟩
    rcases hb with hb | hb
    · exfalso
      have hb4 : (0:ℤ) ≤ b ^ 4 := by positivity
      linarith [hb ▸ hXneg]
    · exact hb
end Table6
