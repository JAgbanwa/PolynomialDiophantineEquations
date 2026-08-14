import RequestProject.SumFourthPowers
/-!
# Divisors of `z⁴ + t⁴` without a coprimality assumption
The results of `RequestProject.SumFourthPowers` concern a *primitive* sum of two
fourth powers.  Here we remove the coprimality hypothesis.  The key observation
is that if `p` is an odd prime with `p ≢ 1 (mod 8)` dividing `z⁴ + t⁴`, then `p`
divides both `z` and `t`; consequently the exponent of `p` in `z⁴ + t⁴` is
divisible by `4`.
The main consequences are:
* `SumFourthPowers.four_dvd_or_sixteen_dvd`: if `4 ∣ z⁴ + t⁴` then `16 ∣ z⁴ + t⁴`;
* `SumFourthPowers.exact_divisor_mod_eight`: if `z⁴ + t⁴ = F * G` with `F` odd and
  `F`, `G` coprime, then `|F| ≡ 1 (mod 8)`.
-/
namespace SumFourthPowers
/-! ## Odd primes that are not `1 (mod 8)` -/
/-- If an odd prime `p` with `p % 8 ≠ 1` divides `z⁴ + t⁴`, it divides both `z` and `t`. -/
theorem prime_dvd_both (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) (z t : ℤ)
    (hdvd : (p : ℤ) ∣ z ^ 4 + t ^ 4) : (p : ℤ) ∣ z ∧ (p : ℤ) ∣ t := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases ht : (p : ℤ) ∣ t
  · refine ⟨?_, ht⟩
    have ht4 : (p : ℤ) ∣ t ^ 4 := ht.pow (by norm_num)
    have hz4 : (p : ℤ) ∣ z ^ 4 := by simpa using dvd_sub hdvd ht4
    exact Int.Prime.dvd_pow' (by exact_mod_cast hp) hz4
  · exfalso
    have htz : ((t : ZMod p)) ≠ 0 := by
      intro h
      exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
    have hzero : ((z : ZMod p)) ^ 4 + ((t : ZMod p)) ^ 4 = 0 := by
      have : ((z ^ 4 + t ^ 4 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
      push_cast at this
      exact this
    refine h8 (prime_mod_eight_of_pow_four_eq_neg_one p hp hp2
      ((z : ZMod p) * (t : ZMod p)⁻¹) ?_)
    field_simp
    linear_combination hzero
/-- For an odd prime `p` with `p % 8 ≠ 1`, the exponent of `p` in `z⁴ + t⁴` is a multiple
of `4`. -/
theorem four_dvd_factorization (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) :
    ∀ n : ℕ, ∀ z t : ℤ, z.natAbs + t.natAbs ≤ n → z ^ 4 + t ^ 4 ≠ 0 →
      4 ∣ ((z ^ 4 + t ^ 4).natAbs.factorization p) := by
  intro n
  induction n with
  | zero =>
    intro z t hle hne
    exfalso
    have hz : z = 0 := by omega
    have ht : t = 0 := by omega
    rw [hz, ht] at hne
    norm_num at hne
  | succ n ih =>
    intro z t hle hne
    by_cases hdvd : (p : ℤ) ∣ z ^ 4 + t ^ 4
    · obtain ⟨hz, ht⟩ := prime_dvd_both p hp hp2 h8 z t hdvd
      obtain ⟨z', rfl⟩ := hz
      obtain ⟨t', rfl⟩ := ht
      have hW : z' ^ 4 + t' ^ 4 ≠ 0 := by
        intro h
        apply hne
        have : ((p : ℤ) * z') ^ 4 + ((p : ℤ) * t') ^ 4 = (p : ℤ) ^ 4 * (z' ^ 4 + t' ^ 4) := by ring
        rw [this, h, mul_zero]
      have hkey : ((p : ℤ) * z') ^ 4 + ((p : ℤ) * t') ^ 4 = (p : ℤ) ^ 4 * (z' ^ 4 + t' ^ 4) := by
        ring
      have hpge : 3 ≤ p := by
        have := hp.two_le
        omega
      have hs : 1 ≤ z'.natAbs + t'.natAbs := by
        rcases Nat.eq_zero_or_pos (z'.natAbs + t'.natAbs) with h | h
        · exfalso
          have hz0 : z' = 0 := by omega
          have ht0 : t' = 0 := by omega
          rw [hz0, ht0] at hW
          norm_num at hW
        · exact h
      have habs : ((p : ℤ) * z').natAbs + ((p : ℤ) * t').natAbs
          = p * (z'.natAbs + t'.natAbs) := by
        simp [Int.natAbs_mul, Nat.mul_add]
      have hle' : z'.natAbs + t'.natAbs ≤ n := by
        rw [habs] at hle
        nlinarith [hs, hpge, hle]
      have hih := ih z' t' hle' hW
      rw [hkey]
      have hpow : ((p : ℤ) ^ 4 * (z' ^ 4 + t' ^ 4)).natAbs
          = p ^ 4 * (z' ^ 4 + t' ^ 4).natAbs := by
        simp [Int.natAbs_mul]
      rw [hpow, Nat.factorization_mul (by positivity) (by simpa using hW),
        hp.factorization_pow]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    · have hnd : ¬ p ∣ (z ^ 4 + t ^ 4).natAbs := by
        intro h
        exact hdvd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
      rw [Nat.factorization_eq_zero_of_not_dvd hnd]
      exact dvd_zero 4
/-! ## The prime `2` -/
/-- If `4` divides `z⁴ + t⁴` then in fact `16` does. -/
theorem four_dvd_or_sixteen_dvd (z t : ℤ) (h : (4 : ℤ) ∣ z ^ 4 + t ^ 4) :
    (16 : ℤ) ∣ z ^ 4 + t ^ 4 := by
  have hboth : z % 2 = 0 ∧ t % 2 = 0 := by
    by_contra hcon
    obtain ⟨k, hk⟩ := h
    rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz | hz <;>
      rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with ht | ht
    · exact hcon ⟨hz, ht⟩
    · have h1 := even_fourth_pow_mod_sixteen z hz
      have h2 := odd_fourth_pow_mod_sixteen t ht
      omega
    · have h1 := odd_fourth_pow_mod_sixteen z hz
      have h2 := even_fourth_pow_mod_sixteen t ht
      omega
    · have h1 := odd_fourth_pow_mod_sixteen z hz
      have h2 := odd_fourth_pow_mod_sixteen t ht
      omega
  obtain ⟨a, ha⟩ : ∃ a, z = 2 * a := ⟨z / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
  exact ⟨a ^ 4 + b ^ 4, by rw [ha, hb]; ring⟩
/-- For `x`, `y` not both even, `x⁴ + y⁴ ≡ 1` or `2 (mod 16)`.  (Version of
`SumFourthPowers.sum_fourth_powers_mod_16` without a coprimality assumption.) -/
theorem sum_fourth_powers_mod_16_of_not_both_even (x y : ℤ) (h : ¬ (x % 2 = 0 ∧ y % 2 = 0)) :
    (x ^ 4 + y ^ 4) % 16 = 1 ∨ (x ^ 4 + y ^ 4) % 16 = 2 := by
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hx | hx <;>
    rcases (show y % 2 = 0 ∨ y % 2 = 1 by omega) with hy | hy
  · exact absurd ⟨hx, hy⟩ h
  · left
    have h1 := even_fourth_pow_mod_sixteen x hx
    have h2 := odd_fourth_pow_mod_sixteen y hy
    omega
  · left
    have h1 := odd_fourth_pow_mod_sixteen x hx
    have h2 := even_fourth_pow_mod_sixteen y hy
    omega
  · right
    have h1 := odd_fourth_pow_mod_sixteen x hx
    have h2 := odd_fourth_pow_mod_sixteen y hy
    omega
/-! ## Exact divisors -/
/-- An odd square is `≡ 1 (mod 8)` (natural-number version). -/
theorem nat_odd_sq_mod_eight (p : ℕ) (h : p % 2 = 1) : p ^ 2 % 8 = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, m * (m + 1) = 2 * j := by
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
    exact ⟨j, by omega⟩
  have : p ^ 2 = 4 * (m * (m + 1)) + 1 := by rw [hm]; ring
  omega
/-- An odd prime power `p ^ k` is `≡ 1 (mod 8)` as soon as `p ≡ 1 (mod 8)` or `k` is even. -/
theorem odd_pow_mod_eight (p k : ℕ) (hp : p % 2 = 1) (h : p % 8 = 1 ∨ 2 ∣ k) :
    p ^ k % 8 = 1 := by
  rcases h with h | ⟨j, hj⟩
  · rw [Nat.pow_mod, h, one_pow]
    norm_num
  · have hsq : p ^ 2 % 8 = 1 := nat_odd_sq_mod_eight p hp
    have hkj : p ^ k = (p ^ 2) ^ j := by rw [hj, ← pow_mul]
    rw [hkj, Nat.pow_mod, hsq, one_pow]
    norm_num
/-- An odd natural number all of whose prime factors are either `≡ 1 (mod 8)` or occur to an
even power is itself `≡ 1 (mod 8)`. -/
theorem odd_mod_eight_of_exponents :
    ∀ F : ℕ, F % 2 = 1 →
      (∀ p : ℕ, p.Prime → p ∣ F → p % 8 = 1 ∨ 2 ∣ F.factorization p) → F % 8 = 1 := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro hodd hfac
    rcases eq_or_lt_of_le (show 1 ≤ F by omega) with h1 | h1
    · omega
    · set p := F.minFac with hpdef
      have hFne : F ≠ 1 := by omega
      have hF0 : F ≠ 0 := by omega
      have hp : p.Prime := Nat.minFac_prime hFne
      have hpdvd : p ∣ F := Nat.minFac_dvd F
      have hp2 : p ≠ 2 := by
        rintro h
        rw [h] at hpdvd
        obtain ⟨k, hk⟩ := hpdvd
        omega
      have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      set k := F.factorization p with hk
      set F₁ := F / p ^ k with hF₁
      have hsplit : p ^ k * F₁ = F := Nat.ordProj_mul_ordCompl_eq_self F p
      have hnotdvd : ¬ p ∣ F₁ := Nat.not_dvd_ordCompl hp hF0
      have hF₁0 : F₁ ≠ 0 := by
        intro h
        rw [h, mul_zero] at hsplit
        omega
      have hkpos : 0 < k := hp.factorization_pos_of_dvd hF0 hpdvd
      have hplt : 1 < p ^ k := by
        have h2 : 2 ≤ p := hp.two_le
        calc 1 < p := h2
          _ ≤ p ^ k := Nat.le_self_pow (by omega) p
      have hF₁lt : F₁ < F := by
        rw [← hsplit]
        nlinarith [Nat.pos_of_ne_zero hF₁0]
      have hF₁odd : F₁ % 2 = 1 := by
        rcases Nat.even_or_odd F₁ with he | ho
        · exfalso
          obtain ⟨c, hc⟩ := he
          have hFe : F = p ^ k * (2 * c) := by rw [← hsplit, hc]; ring
          have h2 : 2 ∣ F := ⟨p ^ k * c, by rw [hFe]; ring⟩
          omega
        · exact Nat.odd_iff.mp ho
      have hfacF : F.factorization = (p ^ k).factorization + F₁.factorization := by
        rw [← Nat.factorization_mul (by positivity) hF₁0, hsplit]
      have hF₁fac : ∀ q : ℕ, q.Prime → q ∣ F₁ → q % 8 = 1 ∨ 2 ∣ F₁.factorization q := by
        intro q hq hqdvd
        have hqF : q ∣ F := hqdvd.trans (Dvd.intro_left _ hsplit)
        have hqp : q ≠ p := by
          rintro rfl
          exact hnotdvd hqdvd
        have hzero : (p ^ k).factorization q = 0 := by
          refine Nat.factorization_eq_zero_of_not_dvd (fun hd => hqp ?_)
          exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
        have hres := hfac q hq hqF
        rw [hfacF] at hres
        simp only [Finsupp.coe_add, Pi.add_apply, hzero, zero_add] at hres
        exact hres
      have hrec := ih F₁ hF₁lt hF₁odd hF₁fac
      have hppow : p ^ k % 8 = 1 := by
        refine odd_pow_mod_eight p k hpodd ?_
        have := hfac p hp hpdvd
        rw [← hk] at this
        exact this
      calc F % 8 = (p ^ k * F₁) % 8 := by rw [hsplit]
        _ = 1 := by rw [Nat.mul_mod, hppow, hrec]
/-- If `z⁴ + t⁴ = F * G` with `F` odd and `F`, `G` coprime, then `|F| ≡ 1 (mod 8)`. -/
theorem exact_divisor_mod_eight (z t F G : ℤ) (hne : z ^ 4 + t ^ 4 ≠ 0)
    (hFG : z ^ 4 + t ^ 4 = F * G) (hcop : IsCoprime F G) (hodd : F % 2 = 1) :
    F.natAbs % 8 = 1 := by
  have hV : (z ^ 4 + t ^ 4).natAbs = F.natAbs * G.natAbs := by rw [hFG, Int.natAbs_mul]
  have hcopn : Nat.Coprime F.natAbs G.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hF0 : F ≠ 0 := by intro h; rw [h, zero_mul] at hFG; exact hne hFG
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hFG; exact hne hFG
  have hFn0 : F.natAbs ≠ 0 := by simpa using hF0
  have hGn0 : G.natAbs ≠ 0 := by simpa using hG0
  refine odd_mod_eight_of_exponents F.natAbs (by omega) ?_
  intro p hp hpdvd
  by_cases h8 : p % 8 = 1
  · exact Or.inl h8
  · refine Or.inr ?_
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hpdvd
      omega
    have hfac4 : 4 ∣ (z ^ 4 + t ^ 4).natAbs.factorization p :=
      four_dvd_factorization p hp hp2 h8 (z.natAbs + t.natAbs) z t le_rfl hne
    have hpG : ¬ p ∣ G.natAbs := fun h => Nat.Prime.one_lt hp |>.ne' (by
      have := Nat.eq_one_of_dvd_coprimes hcopn hpdvd h
      omega)
    rw [hV, Nat.factorization_mul hFn0 hGn0] at hfac4
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_eq_zero_of_not_dvd hpG,
      add_zero] at hfac4
    omega
end SumFourthPowers
