import Mathlib
/-!
# Infinitely Many Integer Solutions for Five Related Diophantine Equations
This file formalises the results of the paper *"Infinitely Many Integer Solutions for Five
Related Diophantine Equations"*.
The paper proves that each of the five equations
* `y² + x³y + z² − 2 = 0`            (E1)
* `y² + x³y + z² + z − 1 = 0`        (E2)
* `y² + x³y + z² + z + 1 = 0`        (E3)
* `y² + x³y + y + z² + 1 = 0`        (E4)
* `y² + x³y + z² + 1 = 0`            (E5)
has infinitely many integer solutions `(x, y, z) ∈ ℤ³`.
The proof is constructive.  The main engine produces, via a Pell-type recurrence, infinitely many
positive integers `N` (of a prescribed parity) for which `N⁶ + c` is a sum of two integer squares,
for the relevant constants `c ∈ {8, 5, −3, −4}`.  A tangent identity supplies an integer identity of
the form `P² + Q² = (N⁶ + c)·(2(u³+c))²`, and a descent lemma (a consequence of Fermat's two squares
theorem) removes the square factor, yielding `N⁶ + c = r² + s²` with `r, s ∈ ℤ`.  Finally these
two-square representations are converted into solutions of the five equations.
-/
open scoped BigOperators
namespace FiveDiophantine
/-! ## §1.  Descent: rational/integral two squares (Lemma 1.2) -/
/-
**Descent for sums of two squares (natural numbers).**
If `M·q²` is a sum of two squares and `q ≠ 0`, then `M` is itself a sum of two squares.
This is the arithmetic heart of Lemma 1.2 of the paper, deduced from Fermat's two squares
theorem (`Nat.eq_sq_add_sq_iff`).
-/
theorem sumsq_descent_nat (M q : ℕ) (hq : q ≠ 0)
    (h : ∃ x y : ℕ, M * q ^ 2 = x ^ 2 + y ^ 2) :
    ∃ r s : ℕ, M = r ^ 2 + s ^ 2 := by
  -- Use Fermat's two squares theorem `Nat.eq_sq_add_sq_iff`.
  have h_fermat : ∀ {n : ℕ}, (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
    apply Nat.eq_sq_add_sq_iff;
  by_cases hM : M = 0 <;> simp_all +decide [ Nat.primeFactors_mul ];
  intro p pp dp hp; specialize h p; simp_all +decide ;
  haveI := Fact.mk pp; rw [ padicValNat.mul ( by positivity ) ( by positivity ), padicValNat.pow ] at h; simp_all +decide [ parity_simps ] ;
  finiteness
/-- **Descent for sums of two squares (integers).**
If `P² + Q² = m · t²` with `t ≠ 0`, then `m` is a sum of two integer squares. -/
theorem sumsq_descent_int (m t : ℤ) (ht : t ≠ 0)
    (h : ∃ P Q : ℤ, P ^ 2 + Q ^ 2 = m * t ^ 2) :
    ∃ r s : ℤ, r ^ 2 + s ^ 2 = m := by
  -- First, we ensure that $m \geq 0$.
  have hm_nonneg : 0 ≤ m := by
    nlinarith [ h.choose_spec.choose_spec, mul_self_pos.2 ht ];
  obtain ⟨ P, Q, h ⟩ := h;
  obtain ⟨ r, s, hr ⟩ := sumsq_descent_nat ( Int.toNat m ) ( Int.natAbs t ) ( by simpa ) ⟨ Int.natAbs P, Int.natAbs Q, by nlinarith [ Int.toNat_of_nonneg hm_nonneg, abs_mul_abs_self t, abs_mul_abs_self P, abs_mul_abs_self Q ] ⟩ ; exact ⟨ r, s, by linarith [ Int.toNat_of_nonneg hm_nonneg ] ⟩ ;
/-! ## §2.  The tangent identity (Lemma 2.1) -/
/-
**Tangent identity (Lemma 2.1).**
Let `a, b, c, u, N, R` be integers with `a² + b² = u³ + c` and
`R² = 4(u³+c)N² − u(u³ − 8c)`.  Then `(N⁶ + c)·(2(u³+c))²` is a sum of two integer squares.
Concretely, with `S = u³ + c` and `L = 3u²N² − u³ + 2c`, the two squares are
`aL − b(N²−u)R` and `bL + a(N²−u)R`.
-/
theorem tangent_sq_identity (a b c u N R : ℤ)
    (hab : a ^ 2 + b ^ 2 = u ^ 3 + c)
    (hR : R ^ 2 = 4 * (u ^ 3 + c) * N ^ 2 - u * (u ^ 3 - 8 * c)) :
    ∃ P Q : ℤ, P ^ 2 + Q ^ 2 = (N ^ 6 + c) * (2 * (u ^ 3 + c)) ^ 2 := by
  -- Set S = u^3 + c and L = 3*u^2*N^2 - u^3 + 2*c.
  set S := u^3 + c
  set L := 3*u^2*N^2 - u^3 + 2*c;
  -- Use P := a*L - b*(N^2-u)*R and Q := b*L + a*(N^2-u)*R as the two squares.
  use a*L - b*(N^2 - u)*R, b*L + a*(N^2 - u)*R;
  grind +ring
/-! ## §2'.  The Pell recurrence (Lemma 2.2) -/
/-- The Pell propagation pair `(Xₖ, Nₖ)` from Lemma 2.2. -/
def pellPair (D P Q X0 N0 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (X0, N0)
  | (k + 1) =>
      (P * (pellPair D P Q X0 N0 k).1 + D * Q * (pellPair D P Q X0 N0 k).2,
       Q * (pellPair D P Q X0 N0 k).1 + P * (pellPair D P Q X0 N0 k).2)
/-
The norm `Xₖ² − D·Nₖ²` is invariant under Pell propagation.
-/
theorem pellPair_norm (D P Q X0 N0 K : ℤ)
    (hunit : P ^ 2 - D * Q ^ 2 = 1) (hinit : X0 ^ 2 - D * N0 ^ 2 = K) :
    ∀ k, (pellPair D P Q X0 N0 k).1 ^ 2 - D * (pellPair D P Q X0 N0 k).2 ^ 2 = K := by
  intro k;
  induction' k with k ih;
  · exact hinit;
  · grind +locals
/-
Both coordinates of the Pell pair stay positive.
-/
theorem pellPair_pos (D P Q X0 N0 : ℤ)
    (hD : 0 < D) (hP : 0 < P) (hQ : 0 < Q) (hX0 : 0 < X0) (hN0 : 0 < N0) :
    ∀ k, 0 < (pellPair D P Q X0 N0 k).1 ∧ 0 < (pellPair D P Q X0 N0 k).2 := by
  intro x; induction x <;> simp +decide [ *, pellPair ] ;
  constructor <;> nlinarith [ mul_pos hD hQ ]
/-
The second coordinate `Nₖ` is strictly increasing.
-/
theorem pellPair_N_strictMono (D P Q X0 N0 : ℤ)
    (hD : 0 < D) (hP : 0 < P) (hQ : 0 < Q) (hX0 : 0 < X0) (hN0 : 0 < N0) :
    StrictMono (fun k => (pellPair D P Q X0 N0 k).2) := by
  refine' strictMono_nat_of_lt_succ _;
  intro n
  simp [pellPair];
  nlinarith [ pellPair_pos D P Q X0 N0 hD hP hQ hX0 hN0 n ]
/-
The parity of `Nₖ` is constant when `P` is odd and `Q` is even.
-/
theorem pellPair_parity (D P Q X0 N0 : ℤ)
    (hPodd : P % 2 = 1) (hQeven : Q % 2 = 0) :
    ∀ k, (pellPair D P Q X0 N0 k).2 % 2 = N0 % 2 := by
  intro k;
  induction' k with k ih;
  · rfl;
  · simp [pellPair, Int.add_emod, Int.mul_emod, hPodd, hQeven, ih]
/-! ## §3.  The core engine -/
/-
**Core engine.**  Combining the tangent identity, the descent lemma and the Pell recurrence,
we obtain a strictly increasing sequence of positive integers `f k`, all of the same parity as
`N0`, such that `(f k)⁶ + c` is a sum of two integer squares.
-/
theorem core_engine (a b c u cst D K X0 N0 P Q : ℤ)
    (hab : a ^ 2 + b ^ 2 = u ^ 3 + c) (hSne : u ^ 3 + c ≠ 0)
    (hD : 0 < D)
    (hrelD : cst ^ 2 * D = 4 * (u ^ 3 + c))
    (hrelK : cst ^ 2 * K = -(u * (u ^ 3 - 8 * c)))
    (hinit : X0 ^ 2 - D * N0 ^ 2 = K) (hunit : P ^ 2 - D * Q ^ 2 = 1)
    (hP : 0 < P) (hQ : 0 < Q) (hX0 : 0 < X0) (hN0 : 0 < N0)
    (hPodd : P % 2 = 1) (hQeven : Q % 2 = 0) :
    ∃ f : ℕ → ℤ, StrictMono f ∧
      ∀ k, 0 < f k ∧ f k % 2 = N0 % 2 ∧ ∃ r s : ℤ, r ^ 2 + s ^ 2 = (f k) ^ 6 + c := by
  refine' ⟨ fun k => ( pellPair D P Q X0 N0 k |> Prod.snd ), _, fun k => ⟨ _, _, _ ⟩ ⟩;
  · convert pellPair_N_strictMono D P Q X0 N0 hD hP hQ hX0 hN0;
  · exact pellPair_pos D P Q X0 N0 hD hP hQ hX0 hN0 k |>.2;
  · exact pellPair_parity D P Q X0 N0 hPodd hQeven k;
  · -- Let $R := cst * Xk$. Then $R^2 = 4*(u^3+c)*Nk^2 - u*(u^3 - 8*c)$.
    set R := cst * (pellPair D P Q X0 N0 k).1
    have hR : R ^ 2 = 4 * (u ^ 3 + c) * (pellPair D P Q X0 N0 k).2 ^ 2 - u * (u ^ 3 - 8 * c) := by
      have := pellPair_norm D P Q X0 N0 K hunit hinit k;
      linear_combination' this * cst ^ 2 + hrelD * ( pellPair D P Q X0 N0 k |>.2 ) ^ 2 + hrelK;
    have := tangent_sq_identity a b c u ( pellPair D P Q X0 N0 k |>.2 ) R hab hR;
    exact sumsq_descent_int _ _ ( by positivity ) this
/-! ## §3'.  Four infinite families of two-square values (Propositions 3.1–3.4) -/
/-
**Proposition 3.1.** Infinitely many positive even `N` with `N⁶ + 8` a sum of two squares.
-/
theorem prop_3_1 :
    ∃ f : ℕ → ℤ, StrictMono f ∧
      ∀ k, 0 < f k ∧ Even (f k) ∧ ∃ r s : ℤ, r ^ 2 + s ^ 2 = (f k) ^ 6 + 8 := by
  convert FiveDiophantine.core_engine 6 22 8 8 4 130 ( -224 ) 136 12 6499 570 _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;> norm_num;
  norm_num [ even_iff_two_dvd ]
/-
**Proposition 3.2.** Infinitely many positive even `N` with `N⁶ + 5` a sum of two squares.
-/
theorem prop_3_2 :
    ∃ f : ℕ → ℤ, StrictMono f ∧
      ∀ k, 0 < f k ∧ Even (f k) ∧ ∃ r s : ℤ, r ^ 2 + s ^ 2 = (f k) ^ 6 + 5 := by
  have := @core_engine;
  convert this 2 3 5 2 2 13 16 22 6 649 180 _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;> norm_num [ Int.even_iff ]
/-
**Proposition 3.3.** Infinitely many positive even `N` with `N⁶ − 3` a sum of two squares.
-/
theorem prop_3_3 :
    ∃ f : ℕ → ℤ, StrictMono f ∧
      ∀ k, 0 < f k ∧ Even (f k) ∧ ∃ r s : ℤ, r ^ 2 + s ^ 2 = (f k) ^ 6 - 3 := by
  convert @core_engine 1 2 ( -3 ) 2 2 5 ( -16 ) 2 2 9 4 _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;> norm_num;
  norm_num [ ← even_iff_two_dvd, parity_simps ];
  rfl
/-
**Proposition 3.4.** Infinitely many positive odd `N` with `N⁶ − 4` a sum of two squares.
-/
theorem prop_3_4 :
    ∃ f : ℕ → ℤ, StrictMono f ∧
      ∀ k, 0 < f k ∧ Odd (f k) ∧ ∃ r s : ℤ, r ^ 2 + s ^ 2 = (f k) ^ 6 - 4 := by
  -- We apply the core engine with the given constants.
  have h_core : ∃ f : ℕ → ℤ, StrictMono f ∧ ∀ k, 0 < f k ∧ f k % 2 = 217898400660155259 % 2 ∧ ∃ r s : ℤ, r^2 + s^2 = (f k)^6 + (-4) := by
    convert core_engine 578 3720 ( -4 ) 242 4 3543121 ( -214359365 ) 410154078658987088294 217898400660155259 53319160674725436041296699414748449 28326330128303226243386806483560 _ _ _ _ _ _ _ _ _ _ _ using 1 <;> norm_num;
  exact h_core.imp fun f hf => ⟨ hf.1, fun k => ⟨ hf.2 k |>.1, Int.odd_iff.mpr ( hf.2 k |>.2.1 ), hf.2 k |>.2.2 ⟩ ⟩
/-! ## §4.  Parity helpers -/
/-
A number `≡ 0 (mod 8)` that is a sum of two squares has both summands even.
-/
theorem even_even_of_sq_add_sq_mod8 (r s : ℤ) (h : (r ^ 2 + s ^ 2) % 8 = 0) :
    Even r ∧ Even s := by
  rcases Int.even_or_odd' r with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' s with ⟨ l, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num at *;
  · lia;
  · exact absurd ( congr_arg ( · % 4 ) h.choose_spec ) ( by norm_num [ Int.add_emod, Int.mul_emod ] );
  · grind
/-
A number `≡ 5 (mod 8)` that is a sum of two squares has exactly one odd summand.
-/
theorem parity_split_of_sq_add_sq_mod8 (r s : ℤ) (h : (r ^ 2 + s ^ 2) % 8 = 5) :
    (Even r ∧ Odd s) ∨ (Odd r ∧ Even s) := by
  rcases Int.even_or_odd' r with ⟨ k, rfl | rfl ⟩ <;> ( ( rcases Int.even_or_odd' s with ⟨ l, rfl | rfl ⟩ ; ( ring_nf at * ; norm_num [ Int.add_emod, Int.mul_emod ] at * ) ) ); all_goals grind
/-! ## §4'.  Pointwise conversions to solutions -/
/-
Conversion for (E1).
-/
theorem conv_E1 (x r s : ℤ) (hx : Even x) (h : r ^ 2 + s ^ 2 = x ^ 6 + 8) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0 := by
  -- Write x = 2*m (use `hx.exists_two_nsmul` or similar; here explicitly `obtain ⟨m, rfl⟩`), x^6 = 64*m^6. Then r^2 + s^2 ≡ 0 (mod 8) because 64*m^6 + 8 ≡ 0 mod 8. By `even_even_of_sq_add_sq_mod8 r s`, both r and s are even.
  obtain ⟨m, rfl⟩ := hx
  have hmod : (r ^ 2 + s ^ 2) % 8 = 0 := by
    grind
  have h_even_r : Even r := by
    exact even_even_of_sq_add_sq_mod8 r s hmod |>.1
  have h_even_s : Even s := by
    exact even_even_of_sq_add_sq_mod8 r s hmod |>.2;
  obtain ⟨ y, rfl ⟩ := h_even_r; obtain ⟨ z, rfl ⟩ := h_even_s; ring_nf at h ⊢;
  exact ⟨ y - m ^ 3 * 4, z, by linarith ⟩
/-
Conversion for (E2).
-/
theorem conv_E2 (x r s : ℤ) (hx : Even x) (h : r ^ 2 + s ^ 2 = x ^ 6 + 5) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, Even a ∧ Odd b ∧ a ^ 2 + b ^ 2 = x ^ 6 + 5 := by
    have := @parity_split_of_sq_add_sq_mod8 r s ?_;
    · rcases this with ( ⟨ hr, hs ⟩ | ⟨ hr, hs ⟩ ) <;> [ exact ⟨ r, s, hr, hs, h ⟩ ; exact ⟨ s, r, hs, hr, by linarith ⟩ ];
    · rw [ h ] ; obtain ⟨ k, rfl ⟩ := hx; ring_nf; norm_num [ Int.add_emod, Int.mul_emod ] ;
  obtain ⟨y, hy⟩ : ∃ y : ℤ, a = 2 * y + x ^ 3 := by
    exact ⟨ ( a - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by simp_all +decide [ parity_simps ] ) ) ] ; ring ⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, b = 2 * z + 1 := by
    exact hab.2.1;
  exact ⟨ y, z, by subst_vars; linarith ⟩
/-
Conversion for (E3).
-/
theorem conv_E3 (x r s : ℤ) (hx : Even x) (h : r ^ 2 + s ^ 2 = x ^ 6 - 3) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a ^ 2 + b ^ 2 = x ^ 6 - 3 ∧ Even a ∧ Odd b := by
    have h_parity : (r ^ 2 + s ^ 2) % 8 = 5 := by
      obtain ⟨ k, rfl ⟩ := hx; ring_nf at h ⊢; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, h ] ;
    rcases parity_split_of_sq_add_sq_mod8 r s h_parity with ( ⟨ hr, hs ⟩ | ⟨ hr, hs ⟩ ) <;> [ exact ⟨ r, s, h, hr, hs ⟩ ; exact ⟨ s, r, by linarith, hs, hr ⟩ ];
  -- Set $y = (a - x^3)/2$ and $z = (b - 1)/2$.
  obtain ⟨y, hy⟩ : ∃ y : ℤ, a = 2 * y + x ^ 3 := by
    exact ⟨ ( a - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by simp_all +decide [ parity_simps ] ) ) ] ; ring ⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, b = 2 * z + 1 := by
    exact hab.2.2;
  exact ⟨ y, z, by subst_vars; linarith ⟩
/-
Conversion for (E4).  Here `N` is even and `x = -N²`.
-/
theorem conv_E4 (N r s : ℤ) (hN : Even N) (h : r ^ 2 + s ^ 2 = N ^ 6 - 3) :
    ∃ y z : ℤ, y ^ 2 + (-N ^ 2) ^ 3 * y + y + z ^ 2 + 1 = 0 := by
  -- Set x := -N^2. First produce a two-square representation of (x^3+1)^2 - 4.
  set x : ℤ := -N^2
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a^2 + b^2 = (x^3 + 1)^2 - 4 := by
    -- By `sq_add_sq_mul` (the Brahmagupta–Fibonacci identity: a = r^2+s^2, b = (N^3)^2+1^2 ⟹ ∃ A B, a*b = A^2+B^2), get integers A, B with
    --   (N^6 - 3) * (N^6 + 1) = A^2 + B^2.
    have h_sq_add_sq_mul : ∃ A B : ℤ, (N^6 - 3) * (N^6 + 1) = A^2 + B^2 := by
      exact ⟨ r * N ^ 3 + s * 1, r * 1 - s * N ^ 3, by rw [ ← h ] ; ring ⟩;
    grind +revert;
  -- Since $N$ is even, $x = -N^2$ is even, $x^3+1$ is odd, and $(x^3+1)^2 - 4 \equiv 5 \pmod{8}$.
  have h_mod : (a^2 + b^2) % 8 = 5 := by
    obtain ⟨ k, rfl ⟩ := hN; ring_nf at hab ⊢; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, hab ] ;
    grind;
  -- By `parity_split_of_sq_add_sq_mod8 a b`, one of a,b is odd and the other even.
  obtain ⟨ha_odd, hb_even⟩ | ⟨ha_even, hb_odd⟩ : (Odd a ∧ Even b) ∨ (Even a ∧ Odd b) := by
    exact Or.symm (parity_split_of_sq_add_sq_mod8 a b h_mod);
  · -- Set y = (a - (x^3 + 1)) / 2 and z = b / 2.
    obtain ⟨y, hy⟩ : ∃ y : ℤ, a = 2 * y + (x^3 + 1) := by
      exact ⟨ ( a - ( x ^ 3 + 1 ) ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by apply_fun Even at *; simp_all +decide [ parity_simps ] ) ) ] ; ring ⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, b = 2 * z := by
      exact even_iff_two_dvd.mp hb_even;
    exact ⟨ y, z, by subst_vars; linarith ⟩;
  · -- With a even, b odd, a^2 + b^2 = (x^3+1)^2 - 4: obtain y with 2*y + (x^3+1) = b (b-(x^3+1) even), and z with 2*z = a.
    obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * y + (x^3 + 1) = b := by
      obtain ⟨ k, rfl ⟩ := hb_odd; obtain ⟨ m, hm ⟩ := hN; replace hab := congr_arg Even hab; simp_all +decide [ parity_simps ] ;
      exact ⟨ k - ( -N ^ 2 ) ^ 3 / 2, by linarith [ Int.ediv_mul_cancel ( show 2 ∣ ( -N ^ 2 ) ^ 3 from dvd_pow ( even_iff_two_dvd.mp ( by simp +decide [ *, parity_simps ] ) ) three_ne_zero ) ] ⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, 2 * z = a := by
      exact ⟨ a / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ha_even ) ] ⟩;
    exact ⟨ y, z, by subst_vars; nlinarith ⟩
/-
Conversion for (E5).
-/
theorem conv_E5 (x r s : ℤ) (hx : Odd x) (h : r ^ 2 + s ^ 2 = x ^ 6 - 4) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0 := by
  -- By `parity_split_of_sq_add_sq_mod8 r s`, either (Even r ∧ Odd s) or (Odd r ∧ Even s).
  by_cases h_cases : (Even r ∧ Odd s) ∨ (Odd r ∧ Even s);
  · obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a ^ 2 + b ^ 2 = x ^ 6 - 4 ∧ Odd a ∧ Even b := by
      grind;
    -- Set $y$ and $z$ using the odd/even split.
    obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * y + x ^ 3 = a := by
      obtain ⟨ k, rfl ⟩ := hab.2.1; obtain ⟨ m, rfl ⟩ := hx; exact ⟨ k - m ^ 3 * 4 - m ^ 2 * 6 - m * 3, by ring ⟩ ;
    obtain ⟨z, hz⟩ : ∃ z : ℤ, 2 * z = b := by
      grind +qlia;
    exact ⟨ y, z, by subst_vars; linarith ⟩;
  · replace h := congr_arg Even h; simp_all +decide [ parity_simps ] ;
    grind
/-! ## §4''.  Generic infinitude lemma -/
/-
If the set of admissible `x`-coordinates is infinite, then so is the solution set.
-/
theorem infinite_of_x_infinite (Sols : Set (ℤ × ℤ × ℤ))
    (hinf : {x : ℤ | ∃ y z : ℤ, (x, y, z) ∈ Sols}.Infinite) : Sols.Infinite := by
  contrapose! hinf;
  exact Set.Finite.subset ( hinf.image fun x => x.1 ) fun x hx => by aesop;
/-! ## §5.  The five theorems -/
/-
**(E1)** `y² + x³y + z² − 2 = 0` has infinitely many integer solutions.
-/
theorem E1_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite := by
  convert Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun k : ℕ => ( ( prop_3_1.choose k, ( conv_E1 ( prop_3_1.choose k ) ( Classical.choose ( prop_3_1.choose_spec.2 k |>.2.2 ) ) ( Classical.choose_spec ( prop_3_1.choose_spec.2 k |>.2.2 ) |> Classical.choose ) ( prop_3_1.choose_spec.2 k |>.2.1 ) ( Classical.choose_spec ( prop_3_1.choose_spec.2 k |>.2.2 ) |> Classical.choose_spec ) ) |> Classical.choose, ( conv_E1 ( prop_3_1.choose k ) ( Classical.choose ( prop_3_1.choose_spec.2 k |>.2.2 ) ) ( Classical.choose_spec ( prop_3_1.choose_spec.2 k |>.2.2 ) |> Classical.choose ) ( prop_3_1.choose_spec.2 k |>.2.1 ) ( Classical.choose_spec ( prop_3_1.choose_spec.2 k |>.2.2 ) |> Classical.choose_spec ) ) |> Classical.choose_spec |> Classical.choose ) ) ) from ?_ ) ( fun k => ?_ ) using 1
  generalize_proofs at *;
  · exact fun a b h => prop_3_1.choose_spec.1.injective <| by injection h;
  · grind
/-
**(E2)** `y² + x³y + z² + z − 1 = 0` has infinitely many integer solutions.
-/
theorem E2_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite := by
  -- Apply the infinite_of_x_infinite lemma with the set Sols and the function f from prop_3_2.
  apply infinite_of_x_infinite;
  -- By definition of $f$, we know that for every $k$, $(f k, y, z) \in Sols$ for some $y$ and $z$.
  obtain ⟨f, hf_mono, hf⟩ := prop_3_2;
  have h_subset : ∀ k, ∃ y z : ℤ, (f k, y, z) ∈ {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0} := by
    exact fun k => by obtain ⟨ r, s, h ⟩ := hf k |>.2.2; exact conv_E2 _ _ _ ( hf k |>.2.1 ) h;
  exact Set.infinite_of_injective_forall_mem hf_mono.injective fun k => h_subset k
/-
**(E3)** `y² + x³y + z² + z + 1 = 0` has infinitely many integer solutions.
-/
theorem E3_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite := by
  intro h;
  obtain ⟨ f, hf_mono, hf ⟩ := prop_3_3;
  -- By `conv_E3`, for each `k`, there exist `y` and `z` such that `(f k, y, z)` is a solution.
  have h_sol : ∀ k, ∃ y z : ℤ, (f k, y, z) ∈ {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0} := by
    exact fun k => by obtain ⟨ r, s, h ⟩ := hf k |>.2.2; exact conv_E3 _ _ _ ( hf k |>.2.1 ) h;
  exact absurd ( Set.infinite_range_of_injective ( show Function.Injective f from hf_mono.injective ) ) ( Set.not_infinite.mpr <| Set.Finite.subset ( h.image fun p : ℤ × ℤ × ℤ => p.1 ) <| by aesop_cat )
/-
**(E4)** `y² + x³y + y + z² + 1 = 0` has infinitely many integer solutions.
-/
theorem E4_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  obtain ⟨ f, hf_mono, hf ⟩ := prop_3_3;
  -- Define g : ℕ → ℤ by g k = -(f k)^2.
  set g : ℕ → ℤ := fun k => -(f k) ^ 2;
  -- Show that the range of $g$ is contained in the set of $x$-coordinates of solutions.
  have h_range : ∀ k, ∃ y z : ℤ, (g k, y, z) ∈ {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0} := by
    intro k
    obtain ⟨r, s, hrs⟩ := hf k |>.2.2
    have := conv_E4 (f k) r s (hf k |>.2.1) hrs
    aesop;
  -- Show that $g$ is injective.
  have h_inj : Function.Injective g := by
    exact fun a b hab => hf_mono.injective <| by nlinarith [ hf a, hf b ] ;
  exact Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun k => ( g k, Classical.choose ( h_range k ), Classical.choose_spec ( h_range k ) |> Classical.choose ) ) from fun a b hab => h_inj <| by injection hab ) fun k => Classical.choose_spec ( h_range k ) |> Classical.choose_spec
/-
**(E5)** `y² + x³y + z² + 1 = 0` has infinitely many integer solutions.
-/
theorem E5_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  obtain ⟨ f, hf_mono, hf ⟩ := prop_3_4;
  -- Now we show that the range of `f` is contained in the set of admissible `x`-coordinates.
  have h_range : Set.range f ⊆ {x : ℤ | ∃ y z : ℤ, (x, y, z) ∈ {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}} := by
    rintro _ ⟨ k, rfl ⟩;
    obtain ⟨ r, s, h ⟩ := hf k |>.2.2; exact conv_E5 _ _ _ ( hf k |>.2.1 ) h;
  exact infinite_of_x_infinite _ ( Set.infinite_of_injective_forall_mem hf_mono.injective fun k => by aesop )
end FiveDiophantine
