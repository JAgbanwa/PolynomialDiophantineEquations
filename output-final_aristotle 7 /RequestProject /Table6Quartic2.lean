import RequestProject.SumFourthPowers
/-!
# The equation `x⁴ + x y³ + z⁴ + t⁴ = 0`
This file studies the homogeneous quartic Diophantine equation
  `x⁴ + x y³ + z⁴ + t⁴ = 0`,                                            (F)
one of the equations of size `H = 64` listed in Table 6 of
B. Grechuk, *A systematic approach to Diophantine equations: open problems*,
as an equation for which **Problem 3** is open.  Problem 3 asks whether a given
homogeneous equation has an integer solution in which *all* variables are
nonzero.
## Main result
`Table6.no_solution_of_isCoprime_zt`: **equation (F) has no integer solution
with `z` and `t` coprime.**
The proof is elementary.  Writing `V = z⁴ + t⁴`, `A = -x`, `B = x + y` and
`C = x² - x y + y²`, equation (F) says exactly
  `V = A * B * C`,   where   `C = B² + 3 A B + 3 A²`   and   `4 C = (2x-y)² + 3y²`.
Since `z` and `t` are coprime, `V > 0`, `V ≡ 1` or `2 (mod 16)`, and every odd
divisor `F` of `V` satisfies `|F| ≡ 1 (mod 8)` (see
`RequestProject.SumFourthPowers`).  Because `C > 0` we get `A B > 0`, and a
case analysis on the parities of `A` and `B` computes `C mod 8` from the
relation `C = B² + 3AB + 3A²`, always giving a value different from `1`
(namely `7`, `5` or `3`), except when `A` and `B` are both even, in which case
`16 ∣ V`.  Each case is therefore contradictory.
This does **not** settle Problem 3 for (F): the equation is homogeneous, so a
hypothetical solution may only be normalised to have `gcd(x, y, z, t) = 1`, and
the argument leaves open the case `gcd(z, t) > 1`.
-/
namespace Table6
open SumFourthPowers
/-- The arithmetic core of the argument, stated abstractly: there is no
factorisation `V = A * B * C` with `C = B² + 3AB + 3A²` and `C > 0` of a
positive integer `V` with `V ≡ 1, 2 (mod 16)` all of whose odd divisors are
`≡ ±1 (mod 8)`. -/
theorem no_factorisation_of_special_shape (V A B C : ℤ)
    (hV16 : V % 16 = 1 ∨ V % 16 = 2) (hVpos : 0 < V)
    (hdiv : ∀ F : ℤ, F % 2 = 1 → F ∣ V → F.natAbs % 8 = 1)
    (heq : V = A * B * C) (hC : C = B ^ 2 + 3 * (A * B) + 3 * A ^ 2) (hCpos : 0 < C) :
    False := by
  -- `A * B > 0`
  have hABpos : 0 < A * B := by nlinarith [heq, hVpos, hCpos]
  rcases (show A % 2 = 0 ∨ A % 2 = 1 by omega) with hA | hA <;>
    rcases (show B % 2 = 0 ∨ B % 2 = 1 by omega) with hB | hB
  · -- both even: `16 ∣ V`
    obtain ⟨a, ha⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
    have : V = 16 * (a * b * (b ^ 2 + 3 * (a * b) + 3 * a ^ 2)) := by
      rw [heq, hC, ha, hb]; ring
    omega
  · -- `A` even, `B` odd
    -- `4 ∤ A`, since `4 ∣ V` is impossible
    have h4 : A % 4 = 2 := by
      rcases (show A % 4 = 0 ∨ A % 4 = 2 by omega) with h | h
      · exfalso
        obtain ⟨k, hk⟩ : ∃ k, A = 4 * k := ⟨A / 4, by omega⟩
        have : V = 4 * (k * B * C) := by rw [heq, hk]; ring
        omega
      · exact h
    obtain ⟨a, ha⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
    have haodd : a % 2 = 1 := by omega
    -- `a * B` is an odd, positive divisor of `V`
    have hdvd : (a * B) ∣ V := ⟨2 * C, by rw [heq, ha]; ring⟩
    have hodd : (a * B) % 2 = 1 := by
      have := Int.mul_emod a B 2
      rw [haodd, hB] at this
      omega
    have hABa : A * B = 2 * (a * B) := by rw [ha]; ring
    have hpos : 0 < a * B := by omega
    have h8 : (a * B) % 8 = 1 := by
      have := hdiv _ hodd hdvd
      omega
    -- mod-8 values of the pieces
    have hA2 : A ^ 2 % 8 = 4 := by
      have hsq : a ^ 2 % 8 = 1 := odd_sq_mod_eight a haodd
      have : A ^ 2 = 4 * a ^ 2 := by rw [ha]; ring
      omega
    have hB2 : B ^ 2 % 8 = 1 := odd_sq_mod_eight B hB
    -- hence `C ≡ 3 (mod 8)`, while `C` is an odd positive divisor of `V`
    have hCodd : C % 2 = 1 := by omega
    have hCdvd : C ∣ V := ⟨A * B, by rw [heq]; ring⟩
    have hC8 : C % 8 = 1 := by
      have := hdiv _ hCodd hCdvd
      omega
    omega
  · -- `A` odd, `B` even
    have h4 : B % 4 = 2 := by
      rcases (show B % 4 = 0 ∨ B % 4 = 2 by omega) with h | h
      · exfalso
        obtain ⟨k, hk⟩ : ∃ k, B = 4 * k := ⟨B / 4, by omega⟩
        have : V = 4 * (A * k * C) := by rw [heq, hk]; ring
        omega
      · exact h
    obtain ⟨b, hb⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
    have hbodd : b % 2 = 1 := by omega
    have hdvd : (A * b) ∣ V := ⟨2 * C, by rw [heq, hb]; ring⟩
    have hodd : (A * b) % 2 = 1 := by
      have := Int.mul_emod A b 2
      rw [hbodd, hA] at this
      omega
    have hABb : A * B = 2 * (A * b) := by rw [hb]; ring
    have hpos : 0 < A * b := by omega
    have h8 : (A * b) % 8 = 1 := by
      have := hdiv _ hodd hdvd
      omega
    have hB2 : B ^ 2 % 8 = 4 := by
      have hsq : b ^ 2 % 8 = 1 := odd_sq_mod_eight b hbodd
      have : B ^ 2 = 4 * b ^ 2 := by rw [hb]; ring
      omega
    have hA2 : A ^ 2 % 8 = 1 := odd_sq_mod_eight A hA
    have hCodd : C % 2 = 1 := by omega
    have hCdvd : C ∣ V := ⟨A * B, by rw [heq]; ring⟩
    have hC8 : C % 8 = 1 := by
      have := hdiv _ hCodd hCdvd
      omega
    omega
  · -- both odd
    have hA2 : A ^ 2 % 8 = 1 := odd_sq_mod_eight A hA
    have hB2 : B ^ 2 % 8 = 1 := odd_sq_mod_eight B hB
    have hodd : (A * B) % 2 = 1 := by
      have := Int.mul_emod A B 2
      rw [hA, hB] at this
      omega
    have hdvd : (A * B) ∣ V := ⟨C, heq⟩
    have h8 : (A * B) % 8 = 1 := by
      have := hdiv _ hodd hdvd
      omega
    have hCodd : C % 2 = 1 := by omega
    have hCdvd : C ∣ V := ⟨A * B, by rw [heq]; ring⟩
    have hC8 : C % 8 = 1 := by
      have := hdiv _ hCodd hCdvd
      omega
    omega
/-- **Equation (F) has no integer solution with `z` and `t` coprime.**
In particular, `x⁴ + x y³ + z⁴ + t⁴ = 0` has no solution in nonzero integers
with `gcd(z, t) = 1`. -/
theorem no_solution_of_isCoprime_zt (x y z t : ℤ) (hzt : IsCoprime z t)
    (h : x ^ 4 + x * y ^ 3 + z ^ 4 + t ^ 4 = 0) : False := by
  have hVpos : 0 < z ^ 4 + t ^ 4 := sum_fourth_powers_pos z t hzt
  have heq : z ^ 4 + t ^ 4 = -x * (x + y) * (x ^ 2 - x * y + y ^ 2) := by linear_combination h
  have hCpos : 0 < x ^ 2 - x * y + y ^ 2 := by
    have hnonneg : 0 ≤ x ^ 2 - x * y + y ^ 2 := by nlinarith [sq_nonneg (2 * x - y), sq_nonneg y]
    rcases eq_or_lt_of_le hnonneg with h0 | h0
    · exfalso
      rw [← h0, mul_zero] at heq
      omega
    · exact h0
  exact no_factorisation_of_special_shape (z ^ 4 + t ^ 4) (-x) (x + y) (x ^ 2 - x * y + y ^ 2)
    (sum_fourth_powers_mod_16 z t hzt) hVpos
    (fun F hF hdvd => odd_dvd_natAbs_mod_eight z t hzt F hF hdvd) heq (by ring) hCpos
end Table6
