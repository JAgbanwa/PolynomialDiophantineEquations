import Mathlib
/-!
# Infinitude of solutions of the auxiliary Pell-type equation
The paper reduces the representability question to an auxiliary equation of the form
`a x² + c = v²` (a special case of equation (10), with `b = 0`).  We prove the
elementary fact that, when `a > 0` is not a perfect square and one integer solution
with `x, v > 0` exists, the equation has infinitely many integer solutions with
`x > 0` (the paper cites [9, Proposition 5.4]/Gauss's theorem for this).
The proof is self-contained: we take a nontrivial unit `P² - a Q² = 1` from
`Pell.exists_of_not_isSquare` and repeatedly apply the norm-multiplication step
`(v, x) ↦ (vP + aQx, vQ + xP)`, which strictly increases `x`.
-/
namespace SumSquares
/-
A nontrivial positive Pell unit for a non-square `a > 0`.
-/
lemma pell_unit_pos {a : ℤ} (ha : 0 < a) (hns : ¬ IsSquare a) :
    ∃ P Q : ℤ, 1 ≤ P ∧ 1 ≤ Q ∧ P ^ 2 - a * Q ^ 2 = 1 := by
  have := Pell.exists_of_not_isSquare ha hns;
  obtain ⟨ x, y, hxy, hy ⟩ := this; exact ⟨ |x|, |y|, abs_pos.mpr ( show x ≠ 0 by rintro rfl; exact hy <| by nlinarith ), abs_pos.mpr hy, by simpa [ sq_abs ] using hxy ⟩ ;
/-
Infinitude of solutions of `a x² + c = v²`.
-/
lemma aux_infinite {a c : ℤ} (ha : 0 < a) (hns : ¬ IsSquare a)
    {x0 v0 : ℤ} (hx0 : 0 < x0) (hv0 : 0 < v0) (hseed : v0 ^ 2 = a * x0 ^ 2 + c) :
    {x : ℤ | 0 < x ∧ ∃ v : ℤ, v ^ 2 = a * x ^ 2 + c}.Infinite := by
  -- We'll prove that the map $n \mapsto (s n).2$ is strictly increasing, where $s n$ is defined recursively.
  have h_strict_mono : ∃ s : ℕ → ℤ × ℤ, (∀ n, 0 < (s n).1 ∧ 0 < (s n).2 ∧ (s n).1 ^ 2 = a * (s n).2 ^ 2 + c) ∧ StrictMono (fun n => (s n).2) := by
    obtain ⟨ P, Q, hP, hQ, h ⟩ := pell_unit_pos ha hns;
    refine' ⟨ fun n => Nat.recOn n ( v0, x0 ) fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ), _, _ ⟩ <;> norm_num;
    · intro n; induction n <;> simp_all +decide ;
      exact ⟨ by nlinarith [ mul_pos ha ( by linarith : 0 < Q ) ], by nlinarith [ mul_pos ha ( by linarith : 0 < Q ) ], by linear_combination' h * ( ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).1 ^ 2 - a * ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).2 ^ 2 ) + ‹0 < ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).1 ∧ 0 < ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).2 ∧ ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).1 ^ 2 = a * ( Nat.rec ( v0, x0 ) ( fun n ih => ( ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P ) ) ‹_› : ℤ × ℤ ).2 ^ 2 + c›.2.2 ⟩;
    · refine' strictMono_nat_of_lt_succ _;
      intro n;
      -- By definition of $s$, we know that $(s n).1 > 0$ and $(s n).2 > 0$ for all $n$.
      have h_pos : ∀ n, 0 < (Nat.rec (v0, x0) (fun n ih => (ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P)) n : ℤ × ℤ).1 ∧ 0 < (Nat.rec (v0, x0) (fun n ih => (ih.1 * P + a * Q * ih.2, ih.1 * Q + ih.2 * P)) n : ℤ × ℤ).2 := by
        intro n; induction n <;> simp_all +decide ;
        constructor <;> nlinarith [ mul_pos ha ( by linarith : 0 < Q ) ];
      nlinarith [ h_pos n, mul_pos ha ( h_pos n |>.2 ) ];
  exact Set.infinite_of_injective_forall_mem h_strict_mono.choose_spec.2.injective fun n => ⟨ h_strict_mono.choose_spec.1 n |>.2.1, _, h_strict_mono.choose_spec.1 n |>.2.2 ⟩
end SumSquares
