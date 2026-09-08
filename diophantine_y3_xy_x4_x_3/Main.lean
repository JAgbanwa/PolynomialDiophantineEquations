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

/-!
# `y³ + xy = x⁴ + x + 3` has no integer solutions

An elementary obstruction. Any integer solution has `y > 1`, `x` even and `y` odd, and the two
"norm" factorisations

* `(y - 1) * D = (x²)² + 2 · 1²`, where `D = y² + y + 1 + x`,
* `(y - ℓ) * C = A² + 2B²`, where `ℓ = 2x - 13`, `C = y² + yℓ + ℓ² + x`,
  `A = x² - 4x + 20`, `B = 7x - 30`,

force the two positive odd integers `D` and `C` to have all their prime divisors congruent to
`1` or `3` modulo `8`, hence to be congruent to `1` or `3` modulo `8` themselves. But modulo `8`
the equation forces `D · C ≡ 7`, a contradiction.
-/

namespace DiophantineY3XY

/-! ## An elementary prime-divisor lemma -/

/-- **Lemma 1 (first half).** If an odd prime `p` divides `a² + 2b²` and does not divide `b`,
then `p ≡ 1` or `3 (mod 8)`: indeed `(a/b)² = -2` in `ZMod p`, and `-2` is a square modulo an
odd prime `p` exactly when `p ≡ 1, 3 (mod 8)`. -/
theorem prime_mod_eight_of_dvd_sq_add_two_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b : ℤ}
    (hdvd : (p : ℤ) ∣ a ^ 2 + 2 * b ^ 2) (hb : ¬ (p : ℤ) ∣ b) :
    p % 8 = 1 ∨ p % 8 = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.exists_sq_eq_neg_two_iff hp2]
  have hb' : ((b : ZMod p)) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h0 : ((a : ZMod p)) ^ 2 + 2 * ((b : ZMod p)) ^ 2 = 0 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at hz
    linear_combination hz
  refine ⟨(a : ZMod p) / (b : ZMod p), ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb' hb')]
  linear_combination -h0

/-- **Lemma 1 (second half).** A nonzero natural number all of whose prime divisors are
congruent to `1` or `3` modulo `8` is itself congruent to `1` or `3` modulo `8`. -/
theorem mod_eight_of_forall_prime_dvd :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 3) →
      n % 8 = 1 ∨ n % 8 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · left; omega
    · have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by rintro rfl; omega
      have hmlt : m < n := by
        have := hp.two_le
        nlinarith [Nat.pos_of_ne_zero hm0]
      have hip := ih m hmlt hm0 (fun q hq hqd => h q hq (hm ▸ hqd.mul_left _))
      have hpp := h _ hp (Nat.minFac_dvd n)
      have key : n % 8 = (n.minFac % 8 * (m % 8)) % 8 := by
        rw [← Nat.mul_mod, ← hm]
      rcases hpp with a | a <;> rcases hip with b | b <;> rw [a, b] at key <;> omega

/-- Integer version of `mod_eight_of_forall_prime_dvd`, phrased in `ZMod 8`. -/
theorem intCast_mod_eight {m : ℤ} (hm : 0 < m)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p % 8 = 1 ∨ p % 8 = 3) :
    (m : ZMod 8) = 1 ∨ (m : ZMod 8) = 3 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
  have hn : n ≠ 0 := by rintro rfl; simp at hm
  have key := mod_eight_of_forall_prime_dvd n hn
    (fun p hp hpd => h p hp (Int.natCast_dvd_natCast.mpr hpd))
  have hc : ((n : ℤ) : ZMod 8) = ((n % 8 : ℕ) : ZMod 8) := by
    push_cast
    rw [ZMod.natCast_mod]
  rcases key with k | k <;> rw [hc, k] <;> norm_num

/-! ## Positivity -/

/-- The right-hand side `x⁴ + x + 3` is always positive. -/
theorem rhs_pos (x : ℤ) : 0 < x ^ 4 + x + 3 := by
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg x, sq_nonneg (x ^ 2)]

/-- Any solution of the equation has `y > 1`. -/
theorem two_le_y {x y : ℤ} (h : y ^ 3 + x * y = x ^ 4 + x + 3) : 2 ≤ y := by
  by_contra hcon
  push Not at hcon
  have hpos := rhs_pos x
  rcases lt_trichotomy y 0 with hy | hy | hy
  · -- `y ≤ -1`: writing `x = -u`, `y = -v` with `u > v² ≥ 1` the left side is at most `(u-1)²`,
    -- which is smaller than the right side `u⁴ - u + 3`.
    have hy1 : y ≤ -1 := by omega
    have hfac : y * (y ^ 2 + x) = x ^ 4 + x + 3 := by linarith
    have hneg : y ^ 2 + x < 0 := by nlinarith
    set u : ℤ := -x with hu
    set v : ℤ := -y with hv
    have hv1 : 1 ≤ v := by omega
    have huv : v ^ 2 + 1 ≤ u := by nlinarith
    have hvu : v ≤ u - 1 := by nlinarith
    have hbound : v * (u - v ^ 2) ≤ (u - 1) * (u - 1) := by nlinarith
    have heq2 : v * (u - v ^ 2) = u ^ 4 - u + 3 := by
      simp only [hu, hv]; nlinarith [h]
    nlinarith [hbound, heq2, sq_nonneg (u - 1), sq_nonneg u]
  · subst hy
    norm_num at h
    omega
  · -- `y = 1` would give `x⁴ = -2`.
    have hy1 : y = 1 := by omega
    subst hy1
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]

/-- `C = y² + yℓ + ℓ² + x` with `ℓ = 2x - 13` is positive, because
`12C = 3(2y + 2x - 13)² + 4(3x - 19)² + 77`. -/
theorem C_pos (x y : ℤ) : 0 < y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x := by
  nlinarith [sq_nonneg (2 * y + 2 * x - 13), sq_nonneg (3 * x - 19)]

/-- An odd prime dividing `1040 = 2⁴ · 5 · 13` is `5` or `13`. -/
theorem prime_dvd_1040 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 1040) :
    p = 5 ∨ p = 13 := by
  have hcop : Nat.Coprime p 16 := ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right 4
  have h65 : p ∣ 5 * 13 := Nat.Coprime.dvd_of_dvd_mul_left hcop (by simpa using h)
  rcases (Nat.Prime.dvd_mul hp).mp h65 with h5 | h13
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13)

/-! ## The nonexistence theorem -/

/-- **Theorem.** There is no pair of integers `(x, y)` satisfying `y³ + xy = x⁴ + x + 3`. -/
theorem no_solutions : ¬ ∃ x y : ℤ, y ^ 3 + x * y = x ^ 4 + x + 3 := by
  rintro ⟨x, y, h⟩
  have hy2 : 2 ≤ y := two_le_y h
  -- the two norm factorisations
  have hD1 : (y - 1) * (y ^ 2 + y + 1 + x) = (x ^ 2) ^ 2 + 2 * 1 ^ 2 := by linear_combination h
  have hC1 : (y - (2 * x - 13)) * (y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x)
      = (x ^ 2 - 4 * x + 20) ^ 2 + 2 * (7 * x - 30) ^ 2 := by linear_combination h
  have hCpos := C_pos x y
  have hDpos : 0 < y ^ 2 + y + 1 + x := by
    rcases mul_pos_iff.mp (by rw [hD1]; positivity :
        (0 : ℤ) < (y - 1) * (y ^ 2 + y + 1 + x)) with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · linarith
  -- parity: `x` is even and `y` is odd
  have hpar : ∀ X Y : ZMod 2, Y ^ 3 + X * Y = X ^ 4 + X + 3 → X = 0 ∧ Y = 1 := by decide
  have hcast2 : ((y : ZMod 2)) ^ 3 + (x : ZMod 2) * (y : ZMod 2)
      = (x : ZMod 2) ^ 4 + (x : ZMod 2) + 3 := by
    have hz := congrArg (fun t : ℤ => (t : ZMod 2)) h
    push_cast at hz
    exact hz
  obtain ⟨hx2, hy2'⟩ := hpar _ _ hcast2
  have hDodd : ¬ ((2 : ℤ) ∣ (y ^ 2 + y + 1 + x)) := by
    intro hd
    have h0 : (((y ^ 2 + y + 1 + x : ℤ)) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd
    push_cast at h0
    rw [hx2, hy2'] at h0
    exact absurd h0 (by decide)
  have hCodd : ¬ ((2 : ℤ) ∣ (y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x)) := by
    intro hd
    have h0 : (((y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x : ℤ)) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd
    push_cast at h0
    rw [hx2, hy2'] at h0
    exact absurd h0 (by decide)
  -- every prime divisor of `D` is `1` or `3` mod `8`
  have hDprimes : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (y ^ 2 + y + 1 + x) → p % 8 = 1 ∨ p % 8 = 3 := by
    intro p hp hpd
    have hp2 : p ≠ 2 := by rintro rfl; exact hDodd (by exact_mod_cast hpd)
    refine prime_mod_eight_of_dvd_sq_add_two_sq hp hp2 (a := x ^ 2) (b := 1) ?_ ?_
    · exact hD1 ▸ hpd.mul_left _
    · intro hcon
      have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hcon
      have h2 := hp.two_le
      omega
  -- every prime divisor of `C` is `1` or `3` mod `8`
  have hCprimes : ∀ p : ℕ, p.Prime →
      (p : ℤ) ∣ (y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x) → p % 8 = 1 ∨ p % 8 = 3 := by
    intro p hp hpd
    have hp2 : p ≠ 2 := by rintro rfl; exact hCodd (by exact_mod_cast hpd)
    have hdvdAB : (p : ℤ) ∣ (x ^ 2 - 4 * x + 20) ^ 2 + 2 * (7 * x - 30) ^ 2 :=
      hC1 ▸ hpd.mul_left _
    by_cases hb : (p : ℤ) ∣ (7 * x - 30)
    · -- then `p` divides both norm coordinates, hence `p ∣ 1040`, so `p = 5` or `p = 13`
      exfalso
      have hB2 : (p : ℤ) ∣ 2 * (7 * x - 30) ^ 2 := (dvd_pow hb two_ne_zero).mul_left 2
      have hA2 : (p : ℤ) ∣ (x ^ 2 - 4 * x + 20) ^ 2 := by
        have hrw : (x ^ 2 - 4 * x + 20) ^ 2
            = ((x ^ 2 - 4 * x + 20) ^ 2 + 2 * (7 * x - 30) ^ 2) - 2 * (7 * x - 30) ^ 2 := by ring
        rw [hrw]; exact dvd_sub hdvdAB hB2
      have hA : (p : ℤ) ∣ (x ^ 2 - 4 * x + 20) :=
        (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hA2
      have h1040 : (p : ℤ) ∣ 1040 := by
        have hrw : (1040 : ℤ) = 49 * (x ^ 2 - 4 * x + 20) - (7 * x - 30) * (7 * x + 2) := by ring
        rw [hrw]; exact dvd_sub (hA.mul_left _) (hb.mul_right _)
      have h1040n : p ∣ 1040 := by exact_mod_cast h1040
      rcases prime_dvd_1040 hp hp2 h1040n with rfl | rfl
      · -- `p = 5`: `(y+1)² ≡ 2 (mod 5)` is impossible
        have key5 : ∀ X Y : ZMod 5, 7 * X - 30 = 0 →
            Y ^ 2 + Y * (2 * X - 13) + (2 * X - 13) ^ 2 + X ≠ 0 := by decide
        have hB5 : 7 * (x : ZMod 5) - 30 = 0 := by
          have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (7 * x - 30) 5).mpr hb
          push_cast at hz
          linear_combination hz
        have hC5 : (y : ZMod 5) ^ 2 + (y : ZMod 5) * (2 * (x : ZMod 5) - 13)
            + (2 * (x : ZMod 5) - 13) ^ 2 + (x : ZMod 5) = 0 := by
          have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
            (y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x) 5).mpr hpd
          push_cast at hz
          linear_combination hz
        exact key5 _ _ hB5 hC5
      · -- `p = 13`: `(2y+3)² ≡ 6 (mod 13)` is impossible
        have key13 : ∀ X Y : ZMod 13, 7 * X - 30 = 0 →
            Y ^ 2 + Y * (2 * X - 13) + (2 * X - 13) ^ 2 + X ≠ 0 := by decide
        have hB13 : 7 * (x : ZMod 13) - 30 = 0 := by
          have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (7 * x - 30) 13).mpr hb
          push_cast at hz
          linear_combination hz
        have hC13 : (y : ZMod 13) ^ 2 + (y : ZMod 13) * (2 * (x : ZMod 13) - 13)
            + (2 * (x : ZMod 13) - 13) ^ 2 + (x : ZMod 13) = 0 := by
          have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
            (y ^ 2 + y * (2 * x - 13) + (2 * x - 13) ^ 2 + x) 13).mpr hpd
          push_cast at hz
          linear_combination hz
        exact key13 _ _ hB13 hC13
    · exact prime_mod_eight_of_dvd_sq_add_two_sq hp hp2 hdvdAB hb
  -- the contradiction: `D ≡ 1, 3`, `C ≡ 1, 3`, but `D · C ≡ 7 (mod 8)`
  have hD8 := intCast_mod_eight hDpos hDprimes
  have hC8 := intCast_mod_eight hCpos hCprimes
  have key8 : ∀ X Y : ZMod 8, Y ^ 3 + X * Y = X ^ 4 + X + 3 →
      (Y ^ 2 + Y + 1 + X) * (Y ^ 2 + Y * (2 * X - 13) + (2 * X - 13) ^ 2 + X) = 7 := by decide
  have hcast8 : ((y : ZMod 8)) ^ 3 + (x : ZMod 8) * (y : ZMod 8)
      = (x : ZMod 8) ^ 4 + (x : ZMod 8) + 3 := by
    have hz := congrArg (fun t : ℤ => (t : ZMod 8)) h
    push_cast at hz
    exact hz
  have hprod := key8 _ _ hcast8
  push_cast at hD8 hC8
  rcases hD8 with a | a <;> rcases hC8 with b | b <;> rw [a, b] at hprod <;>
    exact absurd hprod (by decide)

end DiophantineY3XY
