import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- Every prime `p ≠ 3` dividing `u ^ 2 + u + 1` satisfies `p ≡ 1 (mod 3)`. -/
theorem prime_dvd_sq_add_self_add_one_mod_three
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (u : ℤ) (hdvd : (p : ℤ) ∣ u ^ 2 + u + 1) :
    p % 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set v : ZMod p := (u : ZMod p) with hv
  have hv0 : v ^ 2 + v + 1 = 0 := by
    have : ((u ^ 2 + u + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    push_cast at this
    simpa [hv] using this
  have hcube : v ^ 3 = 1 := by linear_combination (v - 1) * hv0
  have hne1 : v ≠ 1 := by
    intro h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have h30 : (3 : ZMod p) = 0 := by rw [h] at hv0; linear_combination hv0
      simpa using h30
    have hp3' : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hp3')
  have hunit : IsUnit v :=
    IsUnit.of_mul_eq_one (a := v) (b := v ^ 2) (by linear_combination hcube)
  obtain ⟨w, hw⟩ := hunit
  have hw3 : w ^ 3 = 1 := by
    ext
    push_cast
    rw [hw]
    exact hcube
  have hwne : w ≠ 1 := by
    intro h
    apply hne1
    rw [← hw, h]
    rfl
  have hord : orderOf w = 3 := by
    have hdvd3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd3 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hwne
    · exact h
  have hcard : orderOf w ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
  rw [hord, ZMod.card_units_eq_totient, Nat.totient_prime hp] at hcard
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- Every positive divisor of `u ^ 2 + u + 1` that is not divisible by `3`
is congruent to `1` modulo `3`. -/
theorem divisor_of_sq_add_self_add_one_mod_three (u : ℤ) :
    ∀ d : ℕ, 0 < d → (d : ℤ) ∣ u ^ 2 + u + 1 → ¬ (3 ∣ d) → d % 3 = 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hdvd h3
    by_cases h1 : d = 1
    · omega
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := d) h1
      obtain ⟨e, he⟩ := hpd
      have hpne3 : p ≠ 3 := by
        rintro rfl
        exact h3 ⟨e, he⟩
      have hpdvd : (p : ℤ) ∣ u ^ 2 + u + 1 :=
        dvd_trans ⟨(e : ℤ), by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) he⟩ hdvd
      have hpmod : p % 3 = 1 := prime_dvd_sq_add_self_add_one_mod_three p hp hpne3 u hpdvd
      have hepos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · simp at he; omega
        · exact h
      have helt : e < d := by
        have := hp.two_le
        calc e = 1 * e := (one_mul e).symm
          _ < p * e := by
              exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl e) hepos
          _ = d := he.symm
      have hedvd : (e : ℤ) ∣ u ^ 2 + u + 1 :=
        dvd_trans ⟨(p : ℤ), by push_cast [he]; ring⟩ hdvd
      have he3 : ¬ (3 ∣ e) := fun ⟨k, hk⟩ => h3 ⟨p * k, by rw [he, hk]; ring⟩
      have hemod : e % 3 = 1 := ih e helt hepos hedvd he3
      rw [he, Nat.mul_mod, hpmod, hemod]

/-- **Main theorem**: the equation `y ^ 3 + y ^ 2 + x * y = x ^ 4 + 1`
has no solution in integers. -/
theorem no_integer_solution :
    ¬ ∃ x y : ℤ, y ^ 3 + y ^ 2 + x * y = x ^ 4 + 1 := by
  rintro ⟨x, y, h⟩
  set A : ℤ := x ^ 2 + y with hA
  set B : ℤ := x ^ 4 - x ^ 2 * y + y ^ 2 - x ^ 2 + y + x with hB
  have hAB : A * B = (x ^ 3) ^ 2 + x ^ 3 + 1 := by
    rw [hA, hB]; linear_combination h
  have hpos : 0 < (x ^ 3) ^ 2 + x ^ 3 + 1 := by
    nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 3 + 1)]
  -- congruences mod 3
  have hx3 : (x : ZMod 3) = 1 ∧ (y : ZMod 3) = 2 := by
    have hc : ((y ^ 3 + y ^ 2 + x * y : ℤ) : ZMod 3) = ((x ^ 4 + 1 : ℤ) : ZMod 3) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h
    push_cast at hc
    revert hc
    generalize (x : ZMod 3) = a
    generalize (y : ZMod 3) = b
    revert a b
    decide
  -- positivity of A
  have hApos : 0 < A := by
    rcases lt_trichotomy A 0 with hlt | heq | hgt
    · exfalso
      have hy : y ≤ -x ^ 2 - 1 := by rw [hA] at hlt; omega
      have hynonpos : y < 0 := by nlinarith [sq_nonneg x]
      have hkey : 0 ≤ y ^ 2 + y + x := by
        nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (y + x ^ 2 + 1),
          mul_nonneg (by nlinarith : (0:ℤ) ≤ -y - x ^ 2 - 1) (sq_nonneg x)]
      have hprod : y * (y ^ 2 + y + x) = x ^ 4 + 1 := by linear_combination h
      nlinarith [sq_nonneg (x ^ 2), mul_nonpos_of_nonpos_of_nonneg hynonpos.le hkey]
    · rw [heq, zero_mul] at hAB; omega
    · exact hgt
  have hBpos : 0 < B := by nlinarith [hAB, hpos, hApos]
  -- B is a positive divisor of (x^3)^2 + x^3 + 1, congruent to 2 mod 3
  have hBdvd : B ∣ (x ^ 3) ^ 2 + x ^ 3 + 1 := ⟨A, by linarith [hAB, mul_comm A B]⟩
  have hBmod : B % 3 = 2 := by
    have hc : ((B - 2 : ℤ) : ZMod 3) = 0 := by
      rw [hB]
      push_cast
      rw [hx3.1, hx3.2]
      decide
    have hdd : (3 : ℤ) ∣ B - 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
    omega
  have hnat : ((B.toNat : ℤ)) = B := Int.toNat_of_nonneg hBpos.le
  have hdvdnat : ((B.toNat : ℤ)) ∣ (x ^ 3) ^ 2 + x ^ 3 + 1 := by rw [hnat]; exact hBdvd
  have h3nat : ¬ (3 ∣ B.toNat) := by omega
  have hfin := divisor_of_sq_add_self_add_one_mod_three (x ^ 3) B.toNat (by omega) hdvdnat h3nat
  omega
