import Mathlib
/-!
# Sums of two squares: basic infrastructure
This file develops the elementary theory of the set `S₂` of integers that are sums
of two integer squares, following Section 2 of the paper
"On the polynomial values represented by quadratic forms" (Grechuk–Agbanwa).
The key facts are:
* `SqSum` is multiplicative (Brahmagupta–Fibonacci identity), `sqSum_mul`;
* a sum of two squares is never `≡ 3 (mod 4)`, `sqSum_mod4`;
* the "division" property (*) of the paper: if `N` and `N * k` are sums of two
  squares (with `N, k` positive), then so is `k`, `sqSum_div`.
-/
namespace SumSquares
open scoped BigOperators
/-- `n` is a sum of two integer squares. -/
def SqSum (n : ℤ) : Prop := ∃ a b : ℤ, n = a ^ 2 + b ^ 2
lemma sqSum_zero : SqSum 0 := ⟨0, 0, by ring⟩
lemma sqSum_four : SqSum 4 := ⟨2, 0, by ring⟩
/-- The Brahmagupta–Fibonacci identity: `SqSum` is closed under multiplication. -/
lemma sqSum_mul {m n : ℤ} (hm : SqSum m) (hn : SqSum n) : SqSum (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - b * d, a * d + b * c, by ring⟩
/-
A sum of two squares is never congruent to `3` modulo `4`.
-/
lemma sqSum_mod4 {n : ℤ} (h : SqSum n) : n % 4 ≠ 3 := by
  rcases h with ⟨ a, b, rfl ⟩ ; rcases Int.even_or_odd' a with ⟨ a, rfl | rfl ⟩ <;> rcases Int.even_or_odd' b with ⟨ b, rfl | rfl ⟩ <;> ring_nf <;> norm_num;
/-
Bridge between the integer and natural-number notions of a sum of two squares.
-/
lemma sqSum_iff_toNat {n : ℤ} (hn : 0 ≤ n) :
    SqSum n ↔ ∃ a b : ℕ, n.toNat = a ^ 2 + b ^ 2 := by
  constructor;
  · rintro ⟨ a, b, rfl ⟩;
    exact ⟨ a.natAbs, b.natAbs, by nlinarith [ Int.toNat_of_nonneg hn, abs_mul_abs_self a, abs_mul_abs_self b ] ⟩;
  · rintro ⟨ a, b, h ⟩;
    exact ⟨ a, b, by linarith [ Int.toNat_of_nonneg hn ] ⟩
/-
The "division" property (*): if `N` and `N * k` are sums of two squares, with
`N` and `k` positive, then `k` is a sum of two squares.
-/
lemma sqSum_div {N k : ℤ} (hN : 0 < N) (hk : 0 < k)
    (hNs : SqSum N) (hNk : SqSum (N * k)) : SqSum k := by
  -- Let n1 = N.toNat, n2 = k.toNat. Since N,k>0, N*k>0 and (N*k).toNat = n1*n2, n1>0, n2>0.
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℕ, N = n1 := by
    exact Int.eq_ofNat_of_zero_le hN.le
  obtain ⟨n2, hn2⟩ : ∃ n2 : ℕ, k = n2 := by
    exact ⟨ Int.toNat k, by rw [ Int.toNat_of_nonneg hk.le ] ⟩
  have hn1_pos : 0 < n1 := by
    linarith
  have hn2_pos : 0 < n2 := by
    linarith
  have hNk_pos : 0 < N * k := by
    positivity
  have hNk_toNat : (N * k).toNat = n1 * n2 := by
    grind;
  have hN_sq : ∀ q ∈ n1.primeFactors, q % 4 = 3 → Even (padicValNat q n1) := by
    have := Nat.eq_sq_add_sq_iff.mp (by
    convert sqSum_iff_toNat ( by linarith : 0 ≤ N ) |>.1 hNs ; aesop : ∃ a b : ℕ, n1 = a ^ 2 + b ^ 2);
    assumption
  have hNk_sq : ∀ q ∈ (n1 * n2).primeFactors, q % 4 = 3 → Even (padicValNat q (n1 * n2)) := by
    convert Nat.eq_sq_add_sq_iff.mp ( show ∃ x y : ℕ, n1 * n2 = x ^ 2 + y ^ 2 from ?_ ) using 1;
    obtain ⟨ a, b, h ⟩ := hNk; exact ⟨ a.natAbs, b.natAbs, by linarith [ abs_mul_abs_self a, abs_mul_abs_self b, Int.toNat_of_nonneg hNk_pos.le ] ⟩ ;
  have hNk_sq : ∀ q ∈ n2.primeFactors, q % 4 = 3 → Even (padicValNat q n2) := by
    intro q hq hq'; specialize hNk_sq q; simp_all +decide [ Nat.primeFactors_mul, ne_of_gt ] ;
    haveI := Fact.mk hq.1; rw [ padicValNat.mul ( by positivity ) ( by positivity ) ] at hNk_sq; simp_all +decide [ parity_simps ] ;
    exact hNk_sq.mp ( if h : q ∣ n1 then hN_sq q hq.1 h hq' else by rw [ padicValNat.eq_zero_of_not_dvd h ] ; simp +decide );
  have hNk_sq : ∃ a b : ℕ, n2 = a ^ 2 + b ^ 2 := by
    exact Nat.eq_sq_add_sq_iff.mpr hNk_sq;
  exact hn2.symm ▸ by obtain ⟨ a, b, h ⟩ := hNk_sq; exact ⟨ a, b, by linarith ⟩ ;
end SumSquares
