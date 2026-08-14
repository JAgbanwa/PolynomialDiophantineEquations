import Mathlib
/-!
# Which integers are of the form `x³y²` (resp. `x⁴y³`)
Several of the smallest Diophantine equations left open in B. Grechuk,
*A systematic approach to Diophantine equations: open problems*, have the shape
```
x³ y² = f(z)      or      x⁴ y³ = f(z)
```
for a one-variable polynomial `f` (Table 12, for which **Problem 4** — list all integer
solutions or prove that there are infinitely many — is open, and Table 13, for which
**Problem 6** — does an integer solution exist? — is open).
For such an equation the two "outer" variables are pure book-keeping: an integer `n` is
of the form `x³y²` exactly when `n` is a *powerful* number (up to sign), i.e. when every
prime dividing `n` divides it at least twice; and `n` is of the form `x⁴y³` exactly when
no prime divides `n` exactly once, twice or five times.  This file proves those two
characterisations, so that the equations above become purely one-variable questions
about the arithmetic of `f(z)`.
## Main results
* `PowerfulNumbers.exists_cube_mul_sq_iff` — for `n : ℤ`, `n ≠ 0`:
  `(∃ x y : ℤ, n = x³ y²) ↔ ∀ p prime, p ∣ n → p² ∣ n`.
* `PowerfulNumbers.exists_pow_four_mul_cube_iff` — for `n : ℤ`, `n ≠ 0`:
  `(∃ x y : ℤ, n = x⁴ y³) ↔ ∀ p prime, |n|.factorization p ∉ {1, 2, 5}`.
* `PowerfulNumbers.sq_dvd_of_prime_dvd`, `PowerfulNumbers.cube_dvd_of_prime_dvd` — the
  "easy" directions, in the form used to derive congruence obstructions.
-/
namespace PowerfulNumbers
/-! ## The easy directions, over `ℤ` -/
/-- If a prime divides `x³y²`, then its square does. -/
theorem sq_dvd_of_prime_dvd {p x y : ℤ} (hp : Prime p) (h : p ∣ x ^ 3 * y ^ 2) :
    p ^ 2 ∣ x ^ 3 * y ^ 2 := by
  rcases hp.dvd_mul.mp h with h' | h'
  · have hx : p ∣ x := hp.dvd_of_dvd_pow h'
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hx 2 |>.trans ⟨x, by ring⟩) _
  · have hy : p ∣ y := hp.dvd_of_dvd_pow h'
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hy 2) _
/-- If a prime divides `x⁴y³`, then its cube does. -/
theorem cube_dvd_of_prime_dvd {p x y : ℤ} (hp : Prime p) (h : p ∣ x ^ 4 * y ^ 3) :
    p ^ 3 ∣ x ^ 4 * y ^ 3 := by
  rcases hp.dvd_mul.mp h with h' | h'
  · have hx : p ∣ x := hp.dvd_of_dvd_pow h'
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hx 3 |>.trans ⟨x, by ring⟩) _
  · have hy : p ∣ y := hp.dvd_of_dvd_pow h'
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hy 3) _
/-! ## Representability of a natural number -/
/-- A nonzero natural number in which no prime occurs to the first power is a product
`x³ y²`. -/
theorem cube_mul_sq_of_forall_factorization :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → n.factorization p ≠ 1) →
      ∃ x y : ℕ, n = x ^ 3 * y ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hfac
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0) with h1 | h1
    · exact ⟨1, 1, by omega⟩
    · set p := n.minFac with hp'
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      set e := n.factorization p with he
      set m := n / p ^ e with hm
      have hsplit : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
      have hnotdvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn0
      have hm0 : m ≠ 0 := by
        intro h; rw [h, mul_zero] at hsplit; omega
      have hepos : 0 < e := hp.factorization_pos_of_dvd hn0 hpdvd
      have hplt : 1 < p ^ e := by
        have := hp.two_le
        calc 1 < p := this
          _ ≤ p ^ e := Nat.le_self_pow (by omega) p
      have hmlt : m < n := by
        rw [← hsplit]; nlinarith [Nat.pos_of_ne_zero hm0]
      have hfacm : ∀ q : ℕ, q.Prime → m.factorization q ≠ 1 := by
        intro q hq
        have hfacn : n.factorization = (p ^ e).factorization + m.factorization := by
          rw [← Nat.factorization_mul (by positivity) hm0, hsplit]
        by_cases hqp : q = p
        · subst hqp
          intro hcon
          exact hnotdvd ((Nat.Prime.dvd_iff_one_le_factorization hq hm0).mpr (by omega))
        · have hzero : (p ^ e).factorization q = 0 := by
            refine Nat.factorization_eq_zero_of_not_dvd (fun hd => hqp ?_)
            exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
          have := hfac q hq
          rw [hfacn] at this
          simp only [Finsupp.coe_add, Pi.add_apply, hzero, zero_add] at this
          exact this
      obtain ⟨x1, y1, hxy⟩ := ih m hmlt hm0 hfacm
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, e = 3 * a + 2 * b :=
        ⟨e % 2, (e - 3 * (e % 2)) / 2, by have := hfac p hp; omega⟩
      exact ⟨p ^ a * x1, p ^ b * y1, by rw [← hsplit, hxy, hab]; ring⟩
/-- A nonzero natural number in which no prime occurs to the power `1`, `2` or `5` is a
product `x⁴ y³`. -/
theorem pow_four_mul_cube_of_forall_factorization :
    ∀ n : ℕ, n ≠ 0 →
      (∀ p : ℕ, p.Prime → n.factorization p ≠ 1 ∧ n.factorization p ≠ 2 ∧
        n.factorization p ≠ 5) →
      ∃ x y : ℕ, n = x ^ 4 * y ^ 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hfac
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0) with h1 | h1
    · exact ⟨1, 1, by omega⟩
    · set p := n.minFac with hp'
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      set e := n.factorization p with he
      set m := n / p ^ e with hm
      have hsplit : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
      have hnotdvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn0
      have hm0 : m ≠ 0 := by
        intro h; rw [h, mul_zero] at hsplit; omega
      have hepos : 0 < e := hp.factorization_pos_of_dvd hn0 hpdvd
      have hplt : 1 < p ^ e := by
        have := hp.two_le
        calc 1 < p := this
          _ ≤ p ^ e := Nat.le_self_pow (by omega) p
      have hmlt : m < n := by
        rw [← hsplit]; nlinarith [Nat.pos_of_ne_zero hm0]
      have hfacm : ∀ q : ℕ, q.Prime → m.factorization q ≠ 1 ∧ m.factorization q ≠ 2 ∧
          m.factorization q ≠ 5 := by
        intro q hq
        have hfacn : n.factorization = (p ^ e).factorization + m.factorization := by
          rw [← Nat.factorization_mul (by positivity) hm0, hsplit]
        by_cases hqp : q = p
        · subst hqp
          refine ⟨?_, ?_, ?_⟩ <;>
            · intro hcon
              exact hnotdvd ((Nat.Prime.dvd_iff_one_le_factorization hq hm0).mpr (by omega))
        · have hzero : (p ^ e).factorization q = 0 := by
            refine Nat.factorization_eq_zero_of_not_dvd (fun hd => hqp ?_)
            exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
          have := hfac q hq
          rw [hfacn] at this
          simp only [Finsupp.coe_add, Pi.add_apply, hzero, zero_add] at this
          exact this
      obtain ⟨x1, y1, hxy⟩ := ih m hmlt hm0 hfacm
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, e = 4 * a + 3 * b :=
        ⟨e % 3, (e - 4 * (e % 3)) / 3, by have := hfac p hp; omega⟩
      exact ⟨p ^ a * x1, p ^ b * y1, by rw [← hsplit, hxy, hab]; ring⟩
/-! ## The characterisations over `ℤ` -/
/-- **An integer is a product `x³ y²` exactly when it is powerful**: every prime that
divides it divides it at least twice. -/
theorem exists_cube_mul_sq_iff {n : ℤ} (hn : n ≠ 0) :
    (∃ x y : ℤ, n = x ^ 3 * y ^ 2) ↔ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → ((p : ℤ)) ^ 2 ∣ n := by
  constructor
  · rintro ⟨x, y, rfl⟩ p hp hdvd
    exact sq_dvd_of_prime_dvd (Nat.prime_iff_prime_int.mp hp) hdvd
  · intro hpow
    have hN0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have hfac : ∀ p : ℕ, p.Prime → n.natAbs.factorization p ≠ 1 := by
      intro p hp hcon
      have hpn : p ∣ n.natAbs := (Nat.Prime.dvd_iff_one_le_factorization hp hN0).mpr (by omega)
      have hdvd : (p : ℤ) ∣ n :=
        (Int.natCast_dvd_natCast.mpr hpn).trans (Int.natAbs_dvd.mpr dvd_rfl)
      have h2 : ((p : ℤ)) ^ 2 ∣ n := hpow p hp hdvd
      have : (p ^ 2 : ℕ) ∣ n.natAbs := by
        rw [← Int.natAbs_dvd_natAbs] at h2
        simpa using h2
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp hN0).mp this
      omega
    obtain ⟨u, v, huv⟩ := cube_mul_sq_of_forall_factorization n.natAbs hN0 hfac
    have habs : (n.natAbs : ℤ) = (u : ℤ) ^ 3 * (v : ℤ) ^ 2 := by exact_mod_cast huv
    rcases Int.natAbs_eq n with h | h
    · exact ⟨(u : ℤ), (v : ℤ), by rw [h, habs]⟩
    · exact ⟨-(u : ℤ), (v : ℤ), by rw [h, habs]; ring⟩
/-- **An integer is a product `x⁴ y³` exactly when no prime divides it exactly once,
twice or five times.** -/
theorem exists_pow_four_mul_cube_iff {n : ℤ} (hn : n ≠ 0) :
    (∃ x y : ℤ, n = x ^ 4 * y ^ 3) ↔
      ∀ p : ℕ, p.Prime → n.natAbs.factorization p ≠ 1 ∧ n.natAbs.factorization p ≠ 2 ∧
        n.natAbs.factorization p ≠ 5 := by
  have hN0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  constructor
  · rintro ⟨x, y, rfl⟩ p hp
    have hx : (x ^ 4 * y ^ 3).natAbs = x.natAbs ^ 4 * y.natAbs ^ 3 := by
      simp [Int.natAbs_mul, Int.natAbs_pow]
    have hx0 : x ≠ 0 ∧ y ≠ 0 := by
      constructor <;> · rintro rfl; simp at hn
    have hxn : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0.1
    have hyn : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0.2
    rw [hx, Nat.factorization_mul (by positivity) (by positivity)]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    omega
  · intro hfac
    obtain ⟨u, v, huv⟩ := pow_four_mul_cube_of_forall_factorization n.natAbs hN0 hfac
    have habs : (n.natAbs : ℤ) = (u : ℤ) ^ 4 * (v : ℤ) ^ 3 := by exact_mod_cast huv
    rcases Int.natAbs_eq n with h | h
    · exact ⟨(u : ℤ), (v : ℤ), by rw [h, habs]⟩
    · exact ⟨(u : ℤ), -(v : ℤ), by rw [h, habs]; ring⟩
end PowerfulNumbers
