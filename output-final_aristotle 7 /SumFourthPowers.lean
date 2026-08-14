import Mathlib
/-!
# Divisors of a primitive sum of two fourth powers
This file collects the classical elementary facts about `N = x⁴ + y⁴` with `x`, `y`
coprime that are used to study two of the open equations of Table 6 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*:
* every odd prime divisor of `N` is `≡ 1 (mod 8)` (`prime_dvd_sum_fourth_powers`),
  hence every odd divisor of `N` is `≡ ±1 (mod 8)` (`odd_dvd_natAbs_mod_eight`);
* `N ≡ 1` or `2 (mod 16)` (`sum_fourth_powers_mod_16`); in particular `4 ∤ N`.
-/
namespace SumFourthPowers
/-! ## Odd prime divisors -/
/-- If `-1` is a fourth power in `ZMod p` for an odd prime `p`, then `p ≡ 1 (mod 8)`. -/
theorem prime_mod_eight_of_pow_four_eq_neg_one (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (u : ZMod p)
    (hu : u ^ 4 = -1) : p % 8 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  haveI : Fact (2 < p) := ⟨hp2⟩
  have hne : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h8 : orderOf u ∣ 8 := orderOf_dvd_of_pow_eq_one (by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hu]; ring)
  have h4 : ¬ (orderOf u ∣ 4) := by
    intro h
    have := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hu] at this; exact hne this
  have hle : orderOf u ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  have hord : orderOf u = 8 := by
    interval_cases h : (orderOf u) <;> simp_all
  have hcard : orderOf u ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hu0)
  rw [hord] at hcard
  have := hp.two_le
  omega
/-- Every odd prime divisor of `x⁴ + y⁴`, for coprime `x` and `y`, is `≡ 1 (mod 8)`. -/
theorem prime_dvd_sum_fourth_powers (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (x y : ℤ)
    (hxy : IsCoprime x y) (hdvd : (p : ℤ) ∣ x ^ 4 + y ^ 4) : p % 8 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy : (y : ZMod p) ≠ 0 := by
    intro h
    have hpy : (p : ℤ) ∣ y := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h
    have hpy4 : (p : ℤ) ∣ y ^ 4 := Dvd.dvd.pow hpy (by norm_num)
    have hpx4 : (p : ℤ) ∣ x ^ 4 := by simpa using dvd_sub hdvd hpy4
    have hpx : (p : ℤ) ∣ x := Int.Prime.dvd_pow' (by exact_mod_cast hp) hpx4
    have hu := hxy.isUnit_of_dvd' hpx hpy
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  have hzero : ((x : ZMod p)) ^ 4 + ((y : ZMod p)) ^ 4 = 0 := by
    have : ((x ^ 4 + y ^ 4 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at this
    exact this
  refine prime_mod_eight_of_pow_four_eq_neg_one p hp h2 ((x : ZMod p) * (y : ZMod p)⁻¹) ?_
  field_simp
  linear_combination hzero
/-- Every odd (natural) divisor of `x⁴ + y⁴`, for coprime `x` and `y`, is `≡ 1 (mod 8)`. -/
theorem odd_nat_dvd_mod_eight (x y : ℤ) (hxy : IsCoprime x y) :
    ∀ m : ℕ, Odd m → (m : ℤ) ∣ x ^ 4 + y ^ 4 → m % 8 = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hodd hdvd
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hodd
    rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h1 | h1
    · omega
    · have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
      have hpm : m.minFac ∣ m := Nat.minFac_dvd m
      have hp2 : m.minFac ≠ 2 := by
        rintro h
        rw [h] at hpm
        obtain ⟨k, hk⟩ := hpm
        omega
      have hpd : ((m.minFac : ℕ) : ℤ) ∣ x ^ 4 + y ^ 4 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm) hdvd
      have hp8 : m.minFac % 8 = 1 := prime_dvd_sum_fourth_powers _ hp hp2 x y hxy hpd
      obtain ⟨m', hm'⟩ := hpm
      have hpge : 2 ≤ m.minFac := hp.two_le
      have hm'ne : m' ≠ 0 := by rintro rfl; omega
      have hm'lt : m' < m := by nlinarith [Nat.pos_of_ne_zero hm'ne]
      have hm'odd : Odd m' := by
        have : Odd (m.minFac * m') := hm' ▸ hodd
        exact (Nat.odd_mul.mp this).2
      have hd : m' ∣ m := ⟨m.minFac, by rw [Nat.mul_comm]; exact hm'⟩
      have hm'dvd : (m' : ℤ) ∣ x ^ 4 + y ^ 4 := dvd_trans (Int.natCast_dvd_natCast.mpr hd) hdvd
      have := ih m' hm'lt hm'odd hm'dvd
      rw [hm', Nat.mul_mod, hp8, this]
/-- Every odd (integer) divisor `F` of `x⁴ + y⁴`, for coprime `x` and `y`, has
`|F| ≡ 1 (mod 8)`. -/
theorem odd_dvd_natAbs_mod_eight (x y : ℤ) (hxy : IsCoprime x y) (F : ℤ) (hF : F % 2 = 1)
    (hdvd : F ∣ x ^ 4 + y ^ 4) : F.natAbs % 8 = 1 := by
  have hodd : Odd F.natAbs := by
    rw [Nat.odd_iff]; omega
  have hdvd' : ((F.natAbs : ℕ) : ℤ) ∣ x ^ 4 + y ^ 4 := (Int.natAbs_dvd).mpr hdvd
  exact odd_nat_dvd_mod_eight x y hxy F.natAbs hodd hdvd'
/-- Every odd (integer) divisor of `x⁴ + y⁴`, for coprime `x` and `y`, is `≡ ±1 (mod 8)`. -/
theorem odd_dvd_mod_eight (x y : ℤ) (hxy : IsCoprime x y) (F : ℤ) (hF : F % 2 = 1)
    (hdvd : F ∣ x ^ 4 + y ^ 4) : F % 8 = 1 ∨ F % 8 = 7 := by
  have := odd_dvd_natAbs_mod_eight x y hxy F hF hdvd
  omega
/-! ## The 2-adic behaviour -/
theorem even_fourth_pow_mod_sixteen (a : ℤ) (h : a % 2 = 0) : a ^ 4 % 16 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  have : a ^ 4 = 16 * k ^ 4 := by rw [hk]; ring
  omega
theorem odd_fourth_pow_mod_sixteen (a : ℤ) (h : a % 2 = 1) : a ^ 4 % 16 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have hid : a ^ 4 = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * (k * (k + 1)) + 1 := by rw [hk]; ring
  obtain ⟨j, hj⟩ : ∃ j, k * (k + 1) = 2 * j := by
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    exact ⟨j, by omega⟩
  omega
/-- An odd square is `≡ 1 (mod 8)`. -/
theorem odd_sq_mod_eight (a : ℤ) (h : a % 2 = 1) : a ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have hid : a ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
  obtain ⟨j, hj⟩ : ∃ j, k * (k + 1) = 2 * j := by
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    exact ⟨j, by omega⟩
  omega
/-- For coprime `x, y`, one has `x⁴ + y⁴ ≡ 1` or `2 (mod 16)`. -/
theorem sum_fourth_powers_mod_16 (x y : ℤ) (hxy : IsCoprime x y) :
    (x ^ 4 + y ^ 4) % 16 = 1 ∨ (x ^ 4 + y ^ 4) % 16 = 2 := by
  have hnot : ¬ (x % 2 = 0 ∧ y % 2 = 0) := by
    rintro ⟨hx2, hy2⟩
    have h2x : (2 : ℤ) ∣ x := by omega
    have h2y : (2 : ℤ) ∣ y := by omega
    have := hxy.isUnit_of_dvd' h2x h2y
    rw [Int.isUnit_iff] at this
    omega
  have hxm : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hym : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hxm with h | h <;> rcases hym with h' | h'
  · exact absurd ⟨h, h'⟩ hnot
  · left
    have hx := even_fourth_pow_mod_sixteen x h
    have hy := odd_fourth_pow_mod_sixteen y h'
    omega
  · left
    have hx := odd_fourth_pow_mod_sixteen x h
    have hy := even_fourth_pow_mod_sixteen y h'
    omega
  · right
    have hx := odd_fourth_pow_mod_sixteen x h
    have hy := odd_fourth_pow_mod_sixteen y h'
    omega
/-- A primitive sum of two fourth powers is positive. -/
theorem sum_fourth_powers_pos (x y : ℤ) (hxy : IsCoprime x y) : 0 < x ^ 4 + y ^ 4 := by
  have hnonneg : (0 : ℤ) ≤ x ^ 4 + y ^ 4 := by positivity
  have hne : x ^ 4 + y ^ 4 ≠ 0 := by
    rcases sum_fourth_powers_mod_16 x y hxy with h | h <;> intro he <;> rw [he] at h <;> norm_num at h
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
/-- If `A * B > 0` and both `|A|` and `|B|` are `≡ 1 (mod 8)`, then `A * B ≡ 1 (mod 8)`. -/
theorem prod_mod_eight (A B : ℤ) (hA : A.natAbs % 8 = 1) (hB : B.natAbs % 8 = 1)
    (hpos : 0 < A * B) : (A * B) % 8 = 1 := by
  have h1 : (A * B).natAbs = A.natAbs * B.natAbs := Int.natAbs_mul A B
  have h2 : (A * B).natAbs % 8 = 1 := by rw [h1, Nat.mul_mod, hA, hB]
  omega
end SumFourthPowers
