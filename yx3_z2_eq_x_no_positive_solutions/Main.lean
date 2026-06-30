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
set_option grind.warning false
/-!
# A Ljunggren–Nagell reduction
Formalisation of the paper "A Ljunggren–Nagell reduction", which proves that the
Diophantine equation `y(x³ − z²) = x` has no solution in positive integers, and more
precisely that the only solution with `x, y ≥ 1` and `z ≥ 0` is `(x, y, z) = (1, 1, 0)`.
The argument reduces the problem to the classical Ljunggren–Nagell input that the equation
`U² + 1 = A⁴B³` has no positive solution.  That input is the single external ingredient of
the paper, so here it is carried as an explicit hypothesis (`LjunggrenNagell`) rather than
re-proved.
-/
namespace LjunggrenNagellReduction
/-- **Theorem 1.1 (Ljunggren–Nagell input).**  The equation `U² + 1 = A⁴B³` has no solution
in integers `U, A, B` with `U ≥ 1` and `A, B ≥ 1`.  This is the only external ingredient of
the paper, and is carried as a hypothesis in the results below. -/
def LjunggrenNagell : Prop :=
  ∀ U A B : ℤ, 1 ≤ U → 1 ≤ A → 1 ≤ B → U ^ 2 + 1 ≠ A ^ 4 * B ^ 3
/-
**Lemma 2.1 (Coprime factors of a square).**  If `r, s` are positive coprime integers
whose product is a square, then both `r` and `s` are squares.
-/
lemma coprime_factors_of_sq {r s c : ℤ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hco : Int.gcd r s = 1) (h : r * s = c ^ 2) :
    (∃ a, r = a ^ 2) ∧ (∃ b, s = b ^ 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, r = a ^ 2 ∨ r = -a ^ 2 := by
    apply Int.sq_of_gcd_eq_one hco h
  obtain ⟨b, hb⟩ : ∃ b : ℤ, s = b ^ 2 ∨ s = -b ^ 2 := by
    have := Int.sq_of_gcd_eq_one ( show Int.gcd s r = 1 from Nat.Coprime.symm hco ) ( by linarith ) ; aesop;
  exact ⟨ ⟨ a, ha.resolve_right ( by nlinarith ) ⟩, ⟨ b, hb.resolve_right ( by nlinarith ) ⟩ ⟩
/-
**Lemma 2.2 (The quotient forced by the equation).**  For a solution with `x, y ≥ 1`,
`z ≥ 0`, we have `y ∣ x`; writing `d = x/y` we get `z² = d(d²y³ − 1)`, and if `z > 0` then
`d²y³ − 1 > 0`.
-/
lemma quotient_forced {x y z : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z)
    (heq : y * (x ^ 3 - z ^ 2) = x) :
    ∃ d : ℤ, 1 ≤ d ∧ x = d * y ∧ z ^ 2 = d * (d ^ 2 * y ^ 3 - 1) ∧
      (0 < z → 0 < d ^ 2 * y ^ 3 - 1) := by
  -- Set d = x/y; then d ≥ 1 (since x ≥ 1, y ≥ 1, d positive integer) and x = d*y.
  obtain ⟨d, hd⟩ : ∃ d, x = d * y := by
    exact exists_eq_mul_left_of_dvd ( dvd_of_mul_right_eq _ heq )
  have hd_pos : 1 ≤ d := by
    nlinarith
  subst hd
  use d
  simp_all +decide [ sq, mul_assoc ];
  exact ⟨ by nlinarith, fun hz' => by nlinarith [ pow_pos ( zero_lt_one.trans_le hy ) 3, pow_pos ( zero_lt_one.trans_le hd_pos ) 2 ] ⟩
/-
**Lemma 2.3 (The square quotient reduction).**  Every solution with `x, y ≥ 1`, `z ≥ 0`
either equals `(1, 1, 0)`, or yields integers `a, u ≥ 1` with `x = a²y`, `z = au` and
`u² + 1 = a⁴y³`.
-/
lemma square_quotient_reduction {x y z : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z)
    (heq : y * (x ^ 3 - z ^ 2) = x) :
    (x = 1 ∧ y = 1 ∧ z = 0) ∨
      ∃ a u : ℤ, 1 ≤ a ∧ 1 ≤ u ∧ x = a ^ 2 * y ∧ z = a * u ∧ u ^ 2 + 1 = a ^ 4 * y ^ 3 := by
  by_cases h_case : z = 0;
  · simp_all +decide [ mul_comm ];
    exact Or.inl ⟨ by nlinarith [ pow_pos ( zero_lt_one.trans_le hx ) 2, pow_pos ( zero_lt_one.trans_le hx ) 3, pow_pos ( zero_lt_one.trans_le hy ) 2, pow_pos ( zero_lt_one.trans_le hy ) 3 ], by nlinarith [ pow_pos ( zero_lt_one.trans_le hx ) 2, pow_pos ( zero_lt_one.trans_le hx ) 3, pow_pos ( zero_lt_one.trans_le hy ) 2, pow_pos ( zero_lt_one.trans_le hy ) 3 ] ⟩;
  · obtain ⟨ d, hd₁, hd₂, hd₃, hd₄ ⟩ := quotient_forced hx hy hz heq;
    -- By `coprime_factors_of_sq`, we get `d = a^2` and `d^2 y^3 - 1 = u^2` with `a, u ≥ 1`.
    obtain ⟨ a, ha₁, ha₂ ⟩ : ∃ a : ℤ, 1 ≤ a ∧ d = a ^ 2 := by
      have h_coprime : Int.gcd d (d ^ 2 * y ^ 3 - 1) = 1 := by
        norm_num [ show d ^ 2 * y ^ 3 - 1 = d * ( d * y ^ 3 ) - 1 by ring ];
      have := coprime_factors_of_sq hd₁ ( show 1 ≤ d ^ 2 * y ^ 3 - 1 from by nlinarith [ hd₄ ( lt_of_le_of_ne hz ( Ne.symm h_case ) ) ] ) h_coprime hd₃.symm;
      rcases this.1 with ⟨ a, rfl ⟩ ; exact ⟨ |a|, by cases abs_cases a <;> nlinarith, by simp +decide ⟩ ;
    obtain ⟨ u, hu₁, hu₂ ⟩ : ∃ u : ℤ, 1 ≤ u ∧ d ^ 2 * y ^ 3 - 1 = u ^ 2 := by
      use Int.natAbs ( z / a );
      simp_all +decide;
      exact ⟨ by rw [ abs_of_nonneg ( Int.ediv_nonneg hz ( by positivity ) ) ] ; exact Int.le_ediv_of_mul_le ( by positivity ) ( by nlinarith [ show z ≥ a by nlinarith [ show 0 < ( a ^ 2 ) ^ 2 * y ^ 3 - 1 from by nlinarith [ hd₄ ( lt_of_le_of_ne hz ( Ne.symm h_case ) ) ] ] ] ), by nlinarith [ Int.ediv_mul_cancel ( show a ∣ z from Int.pow_dvd_pow_iff two_ne_zero |>.1 <| hd₃.symm ▸ dvd_mul_right _ _ ) ] ⟩;
    refine Or.inr ⟨ a, u, ha₁, hu₁, ?_, ?_, ?_ ⟩ <;> subst_vars <;> ring_nf at *;
    · rw [ ← sq_eq_sq₀ ?_ ?_ ] <;> first | positivity | nlinarith;
    · linarith
/-
**Theorem 3.1.**  Assuming the Ljunggren–Nagell input, the only integer solution of
`y(x³ − z²) = x` with `x, y ≥ 1` and `z ≥ 0` is `(x, y, z) = (1, 1, 0)`.
-/
theorem only_solution (hLN : LjunggrenNagell) {x y z : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z) (heq : y * (x ^ 3 - z ^ 2) = x) :
    x = 1 ∧ y = 1 ∧ z = 0 := by
  obtain h | ⟨ a, u, ha, hu, rfl, rfl, h ⟩ := square_quotient_reduction hx hy hz heq <;> simp_all +decide;
  exact absurd ( hLN u a y hu ha hy ) ( by norm_num [ h ] )
/-
**Corollary 3.2.**  Assuming the Ljunggren–Nagell input, the equation `y(x³ − z²) = x`
has no solution in positive integers `x, y, z`.
-/
theorem no_positive_solution (hLN : LjunggrenNagell) {x y z : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    y * (x ^ 3 - z ^ 2) ≠ x := by
  have := LjunggrenNagellReduction.only_solution hLN hx hy ( by linarith );
  grind +splitImp
/-!
## Appendix A. Gaussian-integer form of the quoted input
Here `GaussianInt = ℤ√(-1) = ℤ[i]`, with `Zsqrtd.norm ⟨r, s⟩ = r² + s²`.  We write `U + i` as
the Gaussian integer `⟨U, 1⟩`.
-/
/-- The Gaussian integer `U + i`. -/
def gaussAdd (U : ℤ) : GaussianInt := ⟨U, 1⟩
@[simp] lemma gaussAdd_norm (U : ℤ) : (gaussAdd U).norm = U ^ 2 + 1 := by
  simp [gaussAdd, Zsqrtd.norm_def]; ring
/-
**Proposition A.1 (parity).**  If `U² + 1 = A⁴B³` with `U, A, B ≥ 1`, then `U` is even
and `A` and `B` are odd.
-/
lemma prop_A1_parity {U A B : ℤ} (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : U ^ 2 + 1 = A ^ 4 * B ^ 3) :
    Even U ∧ Odd A ∧ Odd B := by
  apply_fun fun n => n % 4 at h; rcases Int.even_or_odd' U with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' A with ⟨ l, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ m, rfl | rfl ⟩ <;> ring_nf at h <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
  have := Int.emod_nonneg m four_pos.ne'; have := Int.emod_lt_of_pos m four_pos; interval_cases m % 4 <;> contradiction;
/-
**Proposition A.1 (norm converse).**  Taking norms in an identity `U + i = ε·α⁴·β³` with
`ε` a unit recovers an equation of the shape `U² + 1 = N(α)⁴·N(β)³`.  This is the easy half of
the equivalence asserted in Proposition A.1.
-/
lemma prop_A1_norm_converse (U : ℤ) (α β ε : GaussianInt) (hε : IsUnit ε)
    (hfact : gaussAdd U = ε * α ^ 4 * β ^ 3) :
    U ^ 2 + 1 = α.norm ^ 4 * β.norm ^ 3 := by
  have := congr_arg Zsqrtd.norm hfact; norm_num [ pow_succ, mul_assoc ] at this;
  rw [ show Zsqrtd.norm ε = 1 by
        rw [ isUnit_iff_exists_inv ] at hε;
        obtain ⟨ b, hb ⟩ := hε; have := congr_arg Zsqrtd.norm hb; norm_num at this;
        cases' Int.eq_one_or_neg_one_of_mul_eq_one this with h h <;> simp_all +decide [ Zsqrtd.norm ];
        nlinarith ] at this; linear_combination' this;
/-
**Proposition A.1 (coprimality of the factors).**  When `U` is even (equivalently, `U²+1`
is odd), the Gaussian integers `U + i` and `U - i` are coprime in `ℤ[i]`.  This is the key
Gaussian observation underlying the factorisation in Proposition A.1.
-/
lemma prop_A1_coprime {U : ℤ} (hU : Even U) :
    IsCoprime (gaussAdd U) (star (gaussAdd U)) := by
  obtain ⟨ k, hk ⟩ := hU;
  obtain ⟨ a, b, h ⟩ : ∃ a b : ℤ, 2 * a + (U ^ 2 + 1) * b = 1 := by
    exact ⟨ - ( U ^ 2 / 2 ), 1, by linarith [ Int.ediv_mul_cancel ( show 2 ∣ U ^ 2 from even_iff_two_dvd.mp ( by simp +decide [ hk, parity_simps ] ) ) ] ⟩;
  use ⟨ b, 0 ⟩ * star ( gaussAdd U ) + ⟨ 0, -a ⟩, ⟨ 0, a ⟩ ; ext <;> norm_num [ gaussAdd ] <;> ring_nf at h ⊢ ; simp_all +decide [ ← two_mul ] ;
/-
**Proposition A.1 (Gaussian factorisation -- full existence).**  If `U² + 1 = A⁴B³` with
`U, A, B ≥ 1`, then there exist Gaussian integers `α, β` and a unit `ε` with `U + i = ε·α⁴·β³`,
`N(α) = A` and `N(β) = B`.
The statement of this final part of Proposition A.1 is recorded below but is left unproved.
Its proof is the genuine unique-factorisation grouping in `ℤ[i]`: for each rational prime
`ℓ ∣ A⁴B³` (all of which are `≡ 1 mod 4`, hence split as `ℓ = gₗ · conj gₗ`), one must pick
the Gaussian prime `gₗ` of the conjugate pair that actually divides `U + i` (exactly one does,
by `prop_A1_coprime`) and set `α = ∏_{ℓ∣A} gₗ^{vₗ(A)}`, `β = ∏_{ℓ∣B} gₗ^{vₗ(B)}`.  Picking an
arbitrary Gaussian integer of norm `A` does NOT work, because the wrong conjugate fails to be
coprime to `U + i`.  This per-prime valuation bookkeeping in `ℤ[i]` is a substantial development
and is not formalised here.  The provable substance of the appendix is captured by the three
lemmas above (`prop_A1_parity`, `prop_A1_coprime`, `prop_A1_norm_converse`).
theorem prop_A1 {U A B : ℤ} (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : U ^ 2 + 1 = A ^ 4 * B ^ 3) :
    ∃ (α β ε : GaussianInt), IsUnit ε ∧
      gaussAdd U = ε * α ^ 4 * β ^ 3 ∧ α.norm = A ∧ β.norm = B := by
  sorry
-/
end LjunggrenNagellReduction
