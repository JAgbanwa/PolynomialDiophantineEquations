import Mathlib
/-!
# On the polynomial values represented by quadratic forms
This file formalises the main results of the paper
  *On the polynomial values represented by quadratic forms*
  by Bogdan Grechuk and Jamal Agbanwa.
The paper develops an elementary "tangent construction" for proving that the values
`P(x)` of a univariate integer polynomial are represented by a fixed non-degenerate
binary quadratic form for infinitely many integers `x`.  Applied to the sum of two
squares form `y² + z²`, `R(t) = t³ + f` and `Q(x) = x²`, it proves that `x⁶ + f`
is a sum of two squares infinitely often for `f ∈ {8, 5, -3, -4}`, and deduces that
the Diophantine equation `y² + x³y + z² + 1 = 0` (and four further length-9
equations) has infinitely many integer solutions.  Section 4 extends the
construction to arbitrary non-degenerate binary quadratic forms, illustrated by the
non-multiplicative form `2y² + yz + 2z²`.
## Main results
* `Sum2Sq.div`              : the "property (*)" of the set of sums of two squares.
* `genPell_infinite`        : a generalised Pell equation `v² = a x² + c` with `a > 0`
                              non-square, `c ≠ 0` and one solution has infinitely many
                              positive solutions (Gauss's theorem, [9, Prop. 5.4]).
* `genPell_infinite_cong`   : the residue-controlled refinement: infinitely many solutions
                              in any prescribed class modulo `N`.
* `sum2sq_x6_add`           : the core tangent identity: if the auxiliary Pell equation
                              is solvable then `x⁶ + f` is a sum of two squares.
* `prop_3_1`                : `y² + x³y + z² + 1 = 0` has infinitely many integer solutions.
* `prop_3_2_eq14/15/16/17`  : the four length-9 equations (14)–(17) each have infinitely
                              many integer solutions.
* `prop_4_1_core`           : the algebraic tangent identity for a general form.
* `prop_4_1`                : Proposition 4.1, the full infinitude statement for a general
                              non-degenerate form.
* `prop_4_2`                : Proposition 4.2, infinitely many solutions of the auxiliary
                              equation (30) subject to the congruences (28).
* `algorithm_2_2`           : Algorithm 2.2, the sum-of-two-squares recipe, as a theorem.
* `algorithm_4_3`           : Algorithm 4.3, the general-form recipe, as a theorem.
* `prop_4_4a`, `prop_4_4b`  : the equations `2y² + yz + 2z² = x³ ± 1` have infinitely many
                              integer solutions (Proposition 4.4).
* `form2_not_multiplicative`: the form `2y² + yz + 2z²` is not multiplicative (it represents
                              `2` but not `2·2 = 4`).
* `degenerate_factorization`: a form with `Δ = B² − 4AC = 0` factors as `k (n y + m z)²`.
* `degenerate_infinite_iff`,
  `degenerate_case`         : the degenerate case `Δ = 0`: `F(y,z) = P(x)` has infinitely
                              many integer solutions iff the reduced equation `k t² = P(x)`
                              has a solution with `gcd(n,m) ∣ t`.
-/
namespace SumSquaresPaper
open scoped Classical
/-! ## The set of sums of two squares and property (*) -/
/-- An integer is a *sum of two squares* if it equals `a² + b²` for integers `a, b`.
This is the set `S₂` of the paper (extended to all integers; only positive values occur
in the applications). -/
def Sum2Sq (n : ℤ) : Prop := ∃ a b : ℤ, n = a ^ 2 + b ^ 2
lemma sum2sq_sq (a : ℤ) : Sum2Sq (a ^ 2) := ⟨a, 0, by ring⟩
/-- Product of two sums of two squares is a sum of two squares (Brahmagupta–Fibonacci). -/
lemma Sum2Sq.mul {m n : ℤ} (hm : Sum2Sq m) (hn : Sum2Sq n) : Sum2Sq (m * n) := by
  obtain ⟨x, y, rfl⟩ := hm
  obtain ⟨u, v, rfl⟩ := hn
  exact sq_add_sq_mul rfl rfl
/-
Bridge between the integer and the natural-number notions of "sum of two squares".
-/
lemma sum2sq_iff_toNat {n : ℤ} (hn : 0 ≤ n) :
    Sum2Sq n ↔ ∃ x y : ℕ, n.toNat = x ^ 2 + y ^ 2 := by
  constructor <;> intro h <;> rcases h with ⟨ a, b, h ⟩;
  · exact ⟨ a.natAbs, b.natAbs, by linarith [ Int.toNat_of_nonneg hn, abs_mul_abs_self a, abs_mul_abs_self b ] ⟩;
  · exact ⟨ a, b, by linarith [ Int.toNat_of_nonneg hn ] ⟩
/-
The natural-number characterisation of sums of two squares in valuation form.
-/
lemma natS2_iff_valuation {N : ℕ} (hN : 0 < N) :
    (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ↔
      (∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q N)) := by
  constructor;
  · intro hq q hq_prime hq_mod
    by_cases hq_div : q ∣ N;
    · convert Nat.eq_sq_add_sq_iff.mp hq |> fun h => h q ?_ using 1; all_goals aesop;
    · rw [ padicValNat.eq_zero_of_not_dvd hq_div ] ; norm_num;
  · intro h;
    convert Nat.eq_sq_add_sq_iff.mpr _;
    aesop
/-
The division direction of "property (*)" over `ℕ`.
-/
lemma natS2_div {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hSA : ∃ x y : ℕ, A = x ^ 2 + y ^ 2)
    (hSAB : ∃ x y : ℕ, A * B = x ^ 2 + y ^ 2) :
    ∃ x y : ℕ, B = x ^ 2 + y ^ 2 := by
  -- Apply the valuation-form characterisation to A, B, and A*B (all positive, thanks to hA, hB, hSAB).
  have h_valA : ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q A) := by
    exact fun q hq hq' => by have := natS2_iff_valuation hA; aesop;
  have h_valAB : ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q (A * B)) := by
    exact fun q hq hq' => natS2_iff_valuation ( Nat.mul_pos hA hB ) |>.1 hSAB q hq hq';
  apply (natS2_iff_valuation hB) |>.2;
  intro q hq hq'; specialize h_valAB q hq hq'; specialize h_valA q hq hq'; simp_all +decide [ Nat.even_add, padicValNat.mul hA.ne' hB.ne' ] ;
/-
**Property (*)**, division direction: if `a` and `a*b` are sums of two squares
(with `a, b` positive), then so is `b`.
-/
lemma Sum2Sq.div {m n : ℤ} (hm : 0 < m) (hn : 0 < n)
    (hSm : Sum2Sq m) (hSmn : Sum2Sq (m * n)) : Sum2Sq n := by
  -- Apply `sum2sq_iff_toNat` to `hSm` and `hSmn` to obtain the natural-number versions.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, m = M := by
    exact ⟨ Int.toNat m, by rw [ Int.toNat_of_nonneg hm.le ] ⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N := by
    exact ⟨ Int.toNat n, by rw [ Int.toNat_of_nonneg hn.le ] ⟩
  have hM_nat : ∃ x y : ℕ, M = x ^ 2 + y ^ 2 := by
    obtain ⟨ a, b, hab ⟩ := hSm; use a.natAbs, b.natAbs; cases abs_cases a <;> cases abs_cases b <;> nlinarith;
  have hMN_nat : ∃ x y : ℕ, M * N = x ^ 2 + y ^ 2 := by
    obtain ⟨ x, y, h ⟩ := hSmn; exact ⟨ x.natAbs, y.natAbs, by simpa [ ← Int.natCast_inj, hM, hN ] using h ⟩ ;
  obtain ⟨ x, y, h ⟩ := natS2_div ( show 0 < M from by linarith ) ( show 0 < N from by linarith ) hM_nat hMN_nat ; exact ⟨ x, y, by linarith ⟩
/-
No integer congruent to `3 (mod 4)` is a sum of two squares.
-/
lemma not_sum2sq_mod4_three {n : ℤ} (h : n % 4 = 3) : ¬ Sum2Sq n := by
  rintro ⟨ a, b, rfl ⟩ ; exact absurd h ( by norm_num [ sq, Int.add_emod, Int.mul_emod ] ; have := Int.emod_nonneg a four_ne_zero; have := Int.emod_nonneg b four_ne_zero; have := Int.emod_lt_of_pos a four_pos; have := Int.emod_lt_of_pos b four_pos; interval_cases a % 4 <;> interval_cases b % 4 <;> trivial ) ;
/-! ## The generalised Pell equation -/
/-- One step of the Pell "multiplication by the fundamental unit" map, acting on
`(x, v)`. -/
def pellStep (a p q : ℤ) (xv : ℤ × ℤ) : ℤ × ℤ :=
  (xv.2 * q + xv.1 * p, xv.2 * p + a * xv.1 * q)
/-- Iterated Pell step. -/
def pellIter (a p q : ℤ) (base : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => base
  | n + 1 => pellStep a p q (pellIter a p q base n)
/-
Existence of a fundamental unit with positive coordinates.
-/
lemma pell_unit (a : ℤ) (ha : 0 < a) (hns : ¬ IsSquare a) :
    ∃ p q : ℤ, 1 ≤ p ∧ 1 ≤ q ∧ p ^ 2 - a * q ^ 2 = 1 := by
  -- By Pell's equation, there exists a solution $(p, q)$ with $p$ and $q$ positive integers. Use this fact.
  have := Pell.exists_of_not_isSquare ha hns;
  obtain ⟨ x, y, hxy, hy ⟩ := this; exact ⟨ |x|, |y|, abs_pos.mpr ( show x ≠ 0 by rintro rfl; exact hy <| by nlinarith ), abs_pos.mpr hy, by simpa [ abs_mul ] using hxy ⟩ ;
/-
From one solution we obtain a solution with both coordinates `≥ 1`.
-/
lemma pell_base {a c p q : ℤ} (ha : 0 < a) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ^ 2 - a * q ^ 2 = 1) (hc : c ≠ 0)
    (x0 v0 : ℤ) (h0 : v0 ^ 2 = a * x0 ^ 2 + c) :
    ∃ X0 V0 : ℤ, 1 ≤ X0 ∧ 1 ≤ V0 ∧ V0 ^ 2 = a * X0 ^ 2 + c := by
  -- Let's choose $X_0 = |v0|q + |x0|p$ and $V_0 = |v0|p + a|x0|q$.
  use Int.natAbs v0 * q + Int.natAbs x0 * p, Int.natAbs v0 * p + a * Int.natAbs x0 * q;
  refine' ⟨ _, _, _ ⟩;
  · by_cases hx0 : x0 = 0;
    · simp_all +decide;
      exact one_le_mul_of_one_le_of_one_le ( abs_pos.mpr ( show v0 ≠ 0 by aesop ) ) hq;
    · exact le_add_of_nonneg_of_le ( by positivity ) ( by norm_cast; nlinarith [ abs_pos.mpr hx0 ] );
  · by_cases hx0 : x0 = 0;
    · simp_all +decide [ sq ];
      exact one_le_mul_of_one_le_of_one_le ( abs_pos.mpr ( show v0 ≠ 0 by rintro rfl; exact hc ( by linarith ) ) ) hp;
    · exact le_add_of_nonneg_of_le ( by positivity ) ( one_le_mul_of_one_le_of_one_le ( one_le_mul_of_one_le_of_one_le ha ( mod_cast Int.natAbs_pos.mpr hx0 ) ) hq );
  · grind
/-
The invariant maintained by the Pell iteration.
-/
lemma pellIter_inv {a c p q : ℤ} (ha : 0 < a) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ^ 2 - a * q ^ 2 = 1)
    {X0 V0 : ℤ} (hX0 : 1 ≤ X0) (hV0 : 1 ≤ V0) (hsol : V0 ^ 2 = a * X0 ^ 2 + c) :
    ∀ n, 1 ≤ (pellIter a p q (X0, V0) n).1 ∧ 1 ≤ (pellIter a p q (X0, V0) n).2 ∧
      (pellIter a p q (X0, V0) n).2 ^ 2 = a * (pellIter a p q (X0, V0) n).1 ^ 2 + c := by
  intro n;
  induction n <;> simp_all +decide [ pellIter ] ; ring_nf at * ;
  unfold pellStep; simp_all +decide ;
  exact ⟨ by nlinarith, by nlinarith [ mul_pos ha ( by linarith : 0 < ( pellIter a p q ( X0, V0 ) ‹_› ).1 ) ], by linear_combination' hpq * ( ( pellIter a p q ( X0, V0 ) ‹_› ).2 ^ 2 - a * ( pellIter a p q ( X0, V0 ) ‹_› ).1 ^ 2 ) + ‹1 ≤ ( pellIter a p q ( X0, V0 ) _ ).1 ∧ 1 ≤ ( pellIter a p q ( X0, V0 ) _ ).2 ∧ ( pellIter a p q ( X0, V0 ) _ ).2 ^ 2 = a * ( pellIter a p q ( X0, V0 ) _ ).1 ^ 2 + c›.2.2 ⟩ ;
/-
The first coordinate of the Pell iteration is strictly increasing.
-/
lemma pellIter_fst_lt {a c p q : ℤ} (ha : 0 < a) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ^ 2 - a * q ^ 2 = 1)
    {X0 V0 : ℤ} (hX0 : 1 ≤ X0) (hV0 : 1 ≤ V0) (hsol : V0 ^ 2 = a * X0 ^ 2 + c) :
    ∀ n, (pellIter a p q (X0, V0) n).1 < (pellIter a p q (X0, V0) (n + 1)).1 := by
  intros n
  have h_x_y : 1 ≤ (pellIter a p q (X0, V0) n).1 ∧ 1 ≤ (pellIter a p q (X0, V0) n).2 := by
    exact pellIter_inv ha hp hq hpq hX0 hV0 hsol n |>.1 |> fun x => ⟨ x, pellIter_inv ha hp hq hpq hX0 hV0 hsol n |>.2.1 ⟩;
  rw [ show pellIter a p q ( X0, V0 ) ( n + 1 ) = pellStep a p q ( pellIter a p q ( X0, V0 ) n ) from rfl ] ; unfold pellStep; nlinarith;
/-- **Generalised Pell equation** ([9, Proposition 5.4], Gauss's theorem): if `a > 0`
is not a perfect square, `c ≠ 0`, and `v₀² = a x₀² + c` for some integers, then there
are infinitely many *positive* `x` for which `a x² + c` is a perfect square. -/
theorem genPell_infinite {a c : ℤ} (ha : 0 < a) (hns : ¬ IsSquare a) (hc : c ≠ 0)
    (x0 v0 : ℤ) (h0 : v0 ^ 2 = a * x0 ^ 2 + c) :
    {x : ℤ | 1 ≤ x ∧ ∃ v : ℤ, v ^ 2 = a * x ^ 2 + c}.Infinite := by
  obtain ⟨p, q, hp, hq, hpq⟩ := pell_unit a ha hns
  obtain ⟨X0, V0, hX0, hV0, hsol⟩ := pell_base ha hp hq hpq hc x0 v0 h0
  have hmono : StrictMono (fun n => (pellIter a p q (X0, V0) n).1) :=
    strictMono_nat_of_lt_succ (pellIter_fst_lt ha hp hq hpq hX0 hV0 hsol)
  have hrange : (Set.range (fun n => (pellIter a p q (X0, V0) n).1)).Infinite :=
    Set.infinite_range_of_injective hmono.injective
  refine hrange.mono ?_
  rintro _ ⟨n, rfl⟩
  obtain ⟨h1, _, h3⟩ := pellIter_inv ha hp hq hpq hX0 hV0 hsol n
  exact ⟨h1, _, h3⟩
/-! ## Residue-controlled generalised Pell equation
The auxiliary equations arising in Section 4 must be solved subject to congruence
conditions.  We strengthen `genPell_infinite` so that all produced solutions lie in a
prescribed residue class modulo `N`.  The key ingredient is that a suitable power of the
fundamental unit is congruent to the identity `(1, 0)` modulo `N`. -/
/-- A bijective (indeed injective) self-map of a finite type has a positive power equal to
the identity. -/
lemma exists_iterate_eq_id {α : Type*} [Finite α] (f : α → α) (hf : Function.Injective f) :
    ∃ n : ℕ, 0 < n ∧ f^[n] = id := by
  have hb : Function.Bijective f := (Finite.injective_iff_bijective).mp hf
  let e : Equiv.Perm α := Equiv.ofBijective f hb
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite e).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have h1 : ⇑(e ^ n) = (⇑e)^[n] := Equiv.Perm.coe_pow e n
  have h2 : (⇑e : α → α) = f := rfl
  have h3 : (⇑(e ^ n) : α → α) = id := by rw [hpow]; rfl
  rw [h1, h2] at h3
  exact h3
/-- Multiplication of "unit" coordinates in `ℤ[√a]`: `(P, Q) ↦ (P, Q) · (p, q)` where the
unit `(p, q)` represents `p + q√a`.  Thus `unitPow a p q n` represents `(p + q√a)ⁿ`. -/
def unitPow (a p q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => let w := unitPow a p q n; (w.1 * p + a * w.2 * q, w.1 * q + w.2 * p)
/-
The unit power preserves the norm `P² − aQ² = 1`.
-/
lemma unitPow_norm (a p q : ℤ) (hpq : p ^ 2 - a * q ^ 2 = 1) :
    ∀ n, (unitPow a p q n).1 ^ 2 - a * (unitPow a p q n).2 ^ 2 = 1 := by
  intro n
  induction n with
  | zero => simp [unitPow]
  | succ n ih =>
    simp only [unitPow]
    linear_combination (p ^ 2 - a * q ^ 2) * ih + hpq
/-
For a positive unit, the unit powers have positive coordinates.
-/
lemma unitPow_pos (a p q : ℤ) (ha : 0 < a) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ n, 1 ≤ n → 1 ≤ (unitPow a p q n).1 ∧ 1 ≤ (unitPow a p q n).2 := by
  intro n hn; induction hn <;> simp_all +decide [ unitPow ] ;
  constructor <;> nlinarith [ mul_pos ha ( by linarith : 0 < ( unitPow a p q ‹_› ).2 ) ]
/-
Some positive power of the fundamental unit is congruent to the identity `(1, 0)`
modulo `N`.
-/
lemma unitPow_identity_mod (a p q : ℤ) (hpq : p ^ 2 - a * q ^ 2 = 1) (N : ℤ) (hN : 0 < N) :
    ∃ d : ℕ, 1 ≤ d ∧ (unitPow a p q d).1 ≡ 1 [ZMOD N] ∧ (unitPow a p q d).2 ≡ 0 [ZMOD N] := by
  -- Define the transformation $T$ and show it is bijective.
  set T : (ZMod N.toNat) × (ZMod N.toNat) → (ZMod N.toNat) × (ZMod N.toNat) := fun w => (w.1 * p + a * w.2 * q, w.1 * q + w.2 * p);
  obtain ⟨d, hd_pos, hd_id⟩ : ∃ d : ℕ, 0 < d ∧ T^[d] = id := by
    convert exists_iterate_eq_id T _;
    · cases N <;> simp +decide [ ZMod ] at *;
      cases ‹ℕ› <;> [ tauto; infer_instance ];
    · intro x y hxy;
      have h_det : (p : ZMod N.toNat) ^ 2 - a * (q : ZMod N.toNat) ^ 2 = 1 := by
        norm_cast;
        aesop;
      grind +ring;
  -- By definition of $T$, we know that $red(unitPow a p q k) = T^[k] (1, 0)$ for all $k$.
  have h_red_unitPow : ∀ k : ℕ, (unitPow a p q k).1.cast = (T^[k] (1, 0)).1 ∧ (unitPow a p q k).2.cast = (T^[k] (1, 0)).2 := by
    intro k; induction k <;> simp_all +decide [ Function.iterate_succ_apply', unitPow ] ;
    aesop;
  use d; simp_all +decide [ Int.ModEq ] ;
  have h_cong : (unitPow a p q d).1 ≡ 1 [ZMOD N.toNat] ∧ (unitPow a p q d).2 ≡ 0 [ZMOD N.toNat] := by
    erw [ ← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff ] ; aesop;
  simp_all +decide [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ];
  exact ⟨ hd_pos, by simpa [ max_eq_left hN.le ] using h_cong.1, by simpa [ max_eq_left hN.le ] using h_cong.2 ⟩
/-
The Pell iteration preserves the equation `v² = a x² + c` (needs only `P² − aQ² = 1`).
-/
lemma pellIter_norm {a c P Q : ℤ} (hPQ : P ^ 2 - a * Q ^ 2 = 1) {x0 v0 : ℤ}
    (h0 : v0 ^ 2 = a * x0 ^ 2 + c) :
    ∀ n, (pellIter a P Q (x0, v0) n).2 ^ 2
      = a * (pellIter a P Q (x0, v0) n).1 ^ 2 + c := by
  intro n; induction n <;> simp_all +decide [ pellIter, pellStep ] ;
  grind
/-
If the unit is congruent to the identity `(1, 0)` modulo `N`, then the Pell iteration
stays in the residue class of its base modulo `N`.
-/
lemma pellIter_cong {a P Q N : ℤ} (hP : P ≡ 1 [ZMOD N]) (hQ : Q ≡ 0 [ZMOD N]) {x0 v0 : ℤ} :
    ∀ n, (pellIter a P Q (x0, v0) n).1 ≡ x0 [ZMOD N] ∧
      (pellIter a P Q (x0, v0) n).2 ≡ v0 [ZMOD N] := by
  intro n;
  induction' n with n ih;
  · exact ⟨ rfl, rfl ⟩;
  · simp_all +decide [ pellIter, pellStep ];
    simp_all +decide only [Int.ModEq];
    norm_num [ Int.add_emod, Int.mul_emod, hP, hQ, ih ];
    simp +decide [ ← Int.mul_emod ]
/-
The Pell iteration by a positive unit `(P, Q)` (with `P, Q ≥ 1`) starting from a
solution of `v² = a x² + c` (with `c ≠ 0`) is injective in the iteration index.
This is proved by tracking the real quantity `v + x√a`, which is multiplied by
`ρ = P + Q√a > 1` at each step.
-/
lemma pellIter_injective {a c P Q : ℤ} (ha : 0 < a) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hc : c ≠ 0)
    {x0 v0 : ℤ} (h0 : v0 ^ 2 = a * x0 ^ 2 + c) :
    Function.Injective (fun n : ℕ => pellIter a P Q (x0, v0) n) := by
  intro n m hnm
  have hsa : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have h_mul : ∀ n, (pellIter a P Q (x0, v0) n).2 + (pellIter a P Q (x0, v0) n).1 * Real.sqrt (a : ℝ) = (v0 + x0 * Real.sqrt (a : ℝ)) * (P + Q * Real.sqrt (a : ℝ)) ^ n := by
    intro n
    induction n with
    | zero => simp [pellIter]
    | succ n ih =>
      have hstep : pellIter a P Q (x0, v0) (n + 1)
          = pellStep a P Q (pellIter a P Q (x0, v0) n) := rfl
      rw [hstep, pow_succ, ← mul_assoc, ← ih]
      simp only [pellStep]
      push_cast
      linear_combination (-((pellIter a P Q (x0, v0) n).1 : ℝ) * Q) * hsa
  have h_mul_eq : (v0 + x0 * Real.sqrt (a : ℝ)) * (P + Q * Real.sqrt (a : ℝ)) ^ n = (v0 + x0 * Real.sqrt (a : ℝ)) * (P + Q * Real.sqrt (a : ℝ)) ^ m := by
    grind;
  by_cases h : ( v0 + x0 * Real.sqrt a ) = 0 <;> simp_all +decide;
  · -- From $v0 + x0 * \sqrt{a} = 0$, we get $v0 = -x0 * \sqrt{a}$. Squaring both sides gives $v0^2 = a * x0^2$.
    have h_sq : v0 ^ 2 = a * x0 ^ 2 := by
      rw [ ← @Int.cast_inj ℝ ] ; push_cast ; rw [ ← eq_neg_iff_add_eq_zero ] at h ; rw [ h ]
      linear_combination ((x0 : ℝ) ^ 2) * hsa
    aesop;
  · rw [ pow_right_inj₀ ] at h_mul_eq <;> norm_num at *;
    · exact h_mul_eq;
    · positivity;
    · exact ne_of_gt ( lt_add_of_le_of_pos ( mod_cast hP ) ( mul_pos ( by positivity ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) )
/-- **Residue-controlled generalised Pell equation.**  Under the hypotheses of
`genPell_infinite`, and for any modulus `N > 0`, there are infinitely many integer
solutions `(x, v)` of `v² = a x² + c` with `x ≡ x₀` and `v ≡ v₀` modulo `N`. -/
theorem genPell_infinite_cong {a c : ℤ} (ha : 0 < a) (hns : ¬ IsSquare a) (hc : c ≠ 0)
    (N : ℤ) (hN : 0 < N) (x0 v0 : ℤ) (h0 : v0 ^ 2 = a * x0 ^ 2 + c) :
    {p : ℤ × ℤ | p.2 ^ 2 = a * p.1 ^ 2 + c ∧ p.1 ≡ x0 [ZMOD N] ∧ p.2 ≡ v0 [ZMOD N]}.Infinite := by
  obtain ⟨p, q, hp, hq, hpq⟩ := pell_unit a ha hns
  obtain ⟨d, hd, hPd, hQd⟩ := unitPow_identity_mod a p q hpq N hN
  have hPQnorm : (unitPow a p q d).1 ^ 2 - a * (unitPow a p q d).2 ^ 2 = 1 :=
    unitPow_norm a p q hpq d
  have hPpos : 1 ≤ (unitPow a p q d).1 := (unitPow_pos a p q ha hp hq d hd).1
  have hQpos : 1 ≤ (unitPow a p q d).2 := (unitPow_pos a p q ha hp hq d hd).2
  have hinj := pellIter_injective (a := a) (c := c) ha hPpos hQpos hc h0
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨pellIter_norm hPQnorm h0 n, (pellIter_cong hPd hQd n).1, (pellIter_cong hPd hQd n).2⟩
/-! ## The tangent identity for the sum of two squares -/
/-- **The core identity** (Section 2).  Let `R(t) = t³ + f`, `Q(x) = x²`, so that
`P(x) = x⁶ + f`.  If `R(u) = u³ + f` is a positive sum of two squares and the auxiliary
equation `v² = 4(u³+f)x² − u(u³−8f)` holds, then `x⁶ + f` is a sum of two squares. -/
lemma sum2sq_x6_add {f u x v : ℤ} (hupos : 0 < u ^ 3 + f) (huS : Sum2Sq (u ^ 3 + f))
    (hpos : 0 < x ^ 6 + f)
    (hv : v ^ 2 = 4 * (u ^ 3 + f) * x ^ 2 - u * (u ^ 3 - 8 * f)) :
    Sum2Sq (x ^ 6 + f) := by
  have hm : Sum2Sq (4 * (u ^ 3 + f)) := Sum2Sq.mul ⟨2, 0, by ring⟩ huS
  have hmpos : 0 < 4 * (u ^ 3 + f) := by positivity
  have hprod : Sum2Sq (4 * (u ^ 3 + f) * (x ^ 6 + f)) := by
    refine ⟨2 * (u ^ 3 + f) + 3 * u ^ 2 * (x ^ 2 - u), (x ^ 2 - u) * v, ?_⟩
    have : ((x ^ 2 - u) * v) ^ 2
        = (x ^ 2 - u) ^ 2 * (4 * (u ^ 3 + f) * x ^ 2 - u * (u ^ 3 - 8 * f)) := by
      rw [mul_pow, hv]
    rw [this]; ring
  exact Sum2Sq.div hmpos hpos hm hprod
/-! ## Elementary infrastructure for the applications -/
/-- If the set of first coordinates of a ternary relation is infinite, so is the set of
solutions. -/
lemma infinite_triples_of_infinite_fst {R : ℤ → ℤ → ℤ → Prop}
    (h : {x : ℤ | ∃ y z : ℤ, R x y z}.Infinite) :
    {p : ℤ × ℤ × ℤ | R p.1 p.2.1 p.2.2}.Infinite := by
  apply Set.Infinite.of_image (fun p : ℤ × ℤ × ℤ => p.1)
  refine h.mono ?_
  rintro x ⟨y, z, hxyz⟩
  exact ⟨(x, y, z), hxyz, rfl⟩
/-- The image of an infinite set under an injective map is infinite. -/
lemma image_infinite_of_inj {f : ℤ → ℤ} (hf : Function.Injective f)
    {s : Set ℤ} (hs : s.Infinite) : (f '' s).Infinite :=
  hs.image (hf.injOn)
/-! ## Section 3: decomposition lemmas producing explicit solutions -/
/-
If `x` is odd and `x⁶ − 4` is a sum of two squares, equation (2) is solvable.
-/
lemma sol_31 {x : ℤ} (hodd : Odd x) (hS : Sum2Sq (x ^ 6 - 4)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0 := by
  obtain ⟨ A, B, h ⟩ := hS;
  -- Since $x$ is odd, $x^3$ is odd and $x^6 - 4$ is odd, so $A^2 + B^2$ is odd, meaning exactly one of $A, B$ is odd.
  by_cases hA_odd : Odd A;
  · -- Since $A$ is odd, $B$ must be even.
    have hB_even : Even B := by
      replace h := congr_arg Even h; simp_all +decide [ parity_simps ] ;
      grind;
    -- Since $B$ is even, we can write $B = 2z$ for some integer $z$.
    obtain ⟨ z, rfl ⟩ : ∃ z : ℤ, B = 2 * z := by
      exact even_iff_two_dvd.mp hB_even;
    -- Since $A$ is odd, we can write $A = x^3 + 2y$ for some integer $y$.
    obtain ⟨ y, rfl ⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y := by
      exact ⟨ ( A - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by apply_fun Even at *; simp_all +decide [ parity_simps ] ) ) ] ; ring ⟩;
    grind +splitImp;
  · -- Since $B$ is odd, we can write $B = x^3 + 2y$ for some integer $y$.
    obtain ⟨y, hy⟩ : ∃ y : ℤ, B = x ^ 3 + 2 * y := by
      exact ⟨ ( B - x ^ 3 ) / 2, by rw [ mul_comm, Int.ediv_mul_cancel ( even_iff_two_dvd.mp ( by apply_fun Even at *; simp_all +decide [ parity_simps ] ) ) ] ; ring ⟩;
    -- Since $A$ is even, we can write $A = 2z$ for some integer $z$.
    obtain ⟨z, hz⟩ : ∃ z : ℤ, A = 2 * z := by
      exact even_iff_two_dvd.mp ( by simpa using hA_odd );
    exact ⟨ y, z, by subst_vars; linarith ⟩
/-
If `x⁶ − 4` is a positive sum of two squares then `x` is odd.
-/
lemma odd_of_S2_sub4 {x : ℤ} (hpos : 0 < x ^ 6 - 4) (hS : Sum2Sq (x ^ 6 - 4)) : Odd x := by
  by_contra h_even;
  -- Since `x` is even, we can write `x = 2 * w` for some integer `w`.
  obtain ⟨w, rfl⟩ : ∃ w : ℤ, x = 2 * w := by
    exact even_iff_two_dvd.mp <| by simpa using h_even;
  -- Since `Sum2Sq (x^6 - 4) = Sum2Sq (4*(16*w^6 - 1))`, `Sum2Sq 4` (`= 2^2 + 0^2`), `0 < 4` and `0 < 16*w^6 - 1`, property (*) `Sum2Sq.div` gives `Sum2Sq (16*w^6 - 1)`.
  have h_sum2sq : Sum2Sq (16 * w ^ 6 - 1) := by
    convert Sum2Sq.div ( show 0 < 4 by decide ) ( show 0 < 16 * w ^ 6 - 1 by nlinarith [ sq_nonneg ( w ^ 2 ) ] ) _ _ using 1;
    · exact ⟨ 2, 0, by norm_num ⟩;
    · convert hS using 1 ; ring;
  exact not_sum2sq_mod4_three ( show ( 16 * w ^ 6 - 1 ) % 4 = 3 by omega ) h_sum2sq
/-
If `x` is even and `x⁶ + 8` is a sum of two squares, equation (14) is solvable.
-/
lemma sol_14 {x : ℤ} (hx : Even x) (hS : Sum2Sq (x ^ 6 + 8)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0 := by
  obtain ⟨ A, B, h ⟩ := hS;
  -- Since $x$ is even, $x^6 \equiv 0 \pmod{4}$ and $8 \equiv 0 \pmod{4}$, so $A^2 + B^2 \equiv 0 \pmod{4}$, forcing both $A$ and $B$ even.
  have h_even : Even A ∧ Even B := by
    replace h := congr_arg ( · % 4 ) h ; rcases hx with ⟨ k, rfl ⟩ ; rcases Int.even_or_odd' A with ⟨ a, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ b, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
  obtain ⟨ y, rfl ⟩ := h_even.1; obtain ⟨ z, rfl ⟩ := h_even.2; obtain ⟨ w, rfl ⟩ := hx; ring_nf at *;
  exact ⟨ y - w ^ 3 * 4, z, by linarith ⟩
/-
If `x` is even and `x⁶ + 5` is a sum of two squares, equation (15) is solvable.
-/
lemma sol_15 {x : ℤ} (hx : Even x) (hS : Sum2Sq (x ^ 6 + 5)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0 := by
  -- From `hS` obtain `A B : ℤ` with `x^6 + 5 = A^2 + B^2`.
  obtain ⟨A, B, h_eq⟩ : ∃ A B : ℤ, x^6 + 5 = A^2 + B^2 := by
    exact hS;
  obtain ⟨y, z, h_eq⟩ : ∃ y z : ℤ, A = x^3 + 2*y ∧ B = 2*z + 1 ∨ A = 2*y + 1 ∧ B = x^3 + 2*z := by
    rcases Int.even_or_odd' A with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ l, rfl | rfl ⟩;
    · replace h_eq := congr_arg ( · % 4 ) h_eq ; rcases hx with ⟨ m, rfl ⟩ ; ring_nf at h_eq ; norm_num [ Int.add_emod, Int.mul_emod ] at h_eq;
    · exact ⟨ k - x ^ 3 / 2, l, Or.inl ⟨ by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x ^ 3 from dvd_pow ( even_iff_two_dvd.mp hx ) three_ne_zero ) ], rfl ⟩ ⟩;
    · exact ⟨ k, l - x ^ 3 / 2, Or.inr ⟨ by ring, by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x ^ 3 from dvd_pow ( even_iff_two_dvd.mp hx ) three_ne_zero ) ] ⟩ ⟩;
    · replace h_eq := congr_arg ( · % 4 ) h_eq ; rcases hx with ⟨ m, rfl ⟩ ; ring_nf at h_eq ; norm_num [ Int.add_emod, Int.mul_emod ] at h_eq;
  rcases h_eq with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ); all_goals grind
/-
If `x` is even and `x⁶ − 3` is a sum of two squares, equation (16) is solvable.
-/
lemma sol_16 {x : ℤ} (hx : Even x) (hS : Sum2Sq (x ^ 6 - 3)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0 := by
  obtain ⟨ A, B, h ⟩ := hS;
  obtain ⟨ k, hk ⟩ := hx;
  obtain ⟨ y, hy ⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y ∨ B = x ^ 3 + 2 * y := by
    rcases Int.even_or_odd' A with ⟨ y, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ z, rfl | rfl ⟩ <;> subst hk <;> ring_nf at *;
    · exact ⟨ y - k ^ 3 * 4, Or.inl <| by ring ⟩;
    · exact ⟨ y - k ^ 3 * 4, Or.inl <| by ring ⟩;
    · exact ⟨ z - k ^ 3 * 4, Or.inr <| by ring ⟩;
    · grind;
  rcases hy with ( rfl | rfl );
  · -- Since $B$ is odd, we can write $B = 2z + 1$ for some integer $z$.
    obtain ⟨ z, hz ⟩ : ∃ z : ℤ, B = 2 * z + 1 := by
      rcases Int.even_or_odd' B with ⟨ z, rfl | rfl ⟩ <;> replace h := congr_arg Even h <;> simp_all +decide [ parity_simps ];
    exact ⟨ y, z, by subst hz; linarith ⟩;
  · rcases Int.even_or_odd' A with ⟨ z, rfl | rfl ⟩; all_goals grind
/-
If `x` is even and `(x³+1)² − 4` is a sum of two squares, equation (17) is solvable.
-/
lemma sol_17 {x : ℤ} (hx : Even x) (hS : Sum2Sq ((x ^ 3 + 1) ^ 2 - 4)) :
    ∃ y z : ℤ, y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1 = 0 := by
  -- From `hS` obtain `A B : ℤ` with `(x^3+1)^2 - 4 = A^2 + B^2`.
  obtain ⟨A, B, h_eq⟩ : ∃ A B : ℤ, (x ^ 3 + 1) ^ 2 - 4 = A ^ 2 + B ^ 2 := by
    exact hS;
  -- Since `x` is even, `x^3` is even, `x^3 + 1` is odd, so `(x^3+1)^2` is odd and `(x^3+1)^2 - 4` is odd; hence exactly one of `A, B` is odd.
  have h_odd : Odd A ∧ Even B ∨ Even A ∧ Odd B := by
    replace h_eq := congr_arg ( · % 4 ) h_eq ; rcases hx with ⟨ k, rfl ⟩ ; rcases Int.even_or_odd' A with ⟨ m, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ n, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at *;
  obtain ⟨y, z, hyz⟩ : ∃ y z : ℤ, A = x ^ 3 + 2 * y + 1 ∧ B = 2 * z ∨ A = 2 * z ∧ B = x ^ 3 + 2 * y + 1 := by
    rcases h_odd with ( ⟨ ⟨ y, rfl ⟩, ⟨ z, rfl ⟩ ⟩ | ⟨ ⟨ y, rfl ⟩, ⟨ z, rfl ⟩ ⟩ ) <;> simp_all +decide [ parity_simps ];
    · exact ⟨ y - x ^ 3 / 2, z, Or.inl ⟨ by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x ^ 3 from dvd_pow ( even_iff_two_dvd.mp hx ) three_ne_zero ) ], by ring ⟩ ⟩;
    · exact ⟨ z - x ^ 3 / 2, y, Or.inr ⟨ by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x ^ 3 from dvd_pow ( even_iff_two_dvd.mp hx ) three_ne_zero ) ], by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x ^ 3 from dvd_pow ( even_iff_two_dvd.mp hx ) three_ne_zero ) ] ⟩ ⟩;
  rcases hyz with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> exact ⟨ y, z, by linarith ⟩
/-! ## Section 3: infinitude of the relevant sum-of-two-squares sets -/
/-- For `f = -4` and `u = 162`: there are infinitely many odd `x` with `x⁶ − 4 ∈ S₂`. -/
lemma odd_pow6_sub4_S2_infinite :
    {x : ℤ | Odd x ∧ Sum2Sq (x ^ 6 - 4)}.Infinite := by
  have hinf := genPell_infinite (a := 17006096) (c := -688752720)
    (by norm_num) (by native_decide) (by norm_num)
    22108343594783571 91171377945572295096 (by norm_num)
  refine hinf.mono ?_
  rintro x ⟨hx1, v, hv⟩
  have hv' : v ^ 2 = 4 * (162 ^ 3 + (-4 : ℤ)) * x ^ 2 - 162 * (162 ^ 3 - 8 * (-4)) := by
    rw [show (4 * (162 ^ 3 + (-4 : ℤ))) = 17006096 by norm_num,
        show (162 * (162 ^ 3 - 8 * (-4 : ℤ))) = 688752720 by norm_num]; exact hv
  have h40 : (40 : ℤ) < x ^ 2 := by nlinarith [sq_nonneg v, hv]
  have hxsq : (41 : ℤ) ≤ x ^ 2 := by omega
  have hpos : 0 < x ^ 6 - 4 := by
    nlinarith [hxsq, sq_nonneg x, mul_le_mul hxsq hxsq (by norm_num) (by nlinarith [hxsq])]
  have hS : Sum2Sq (x ^ 6 - 4) := by
    have hpos' : 0 < x ^ 6 + (-4 : ℤ) := by linarith
    have := sum2sq_x6_add (f := -4) (u := 162) (x := x) (v := v)
      (by norm_num) (⟨350, 2032, by norm_num⟩) hpos' hv'
    rw [sub_eq_add_neg]; exact this
  exact ⟨odd_of_S2_sub4 hpos hS, hS⟩
/-- For `f = 8` and `u = 8`: there are infinitely many even `x ≥ 0` with `x⁶ + 8 ∈ S₂`. -/
lemma even_pow6_add8_S2_infinite :
    {x : ℤ | 0 ≤ x ∧ Even x ∧ Sum2Sq (x ^ 6 + 8)}.Infinite := by
  have hinf := genPell_infinite (a := 8320) (c := -3584)
    (by norm_num) (by native_decide) (by norm_num) 6 544 (by norm_num)
  refine (image_infinite_of_inj (f := fun w => 2 * w)
    (fun a b h => by simpa using h) hinf).mono ?_
  rintro _ ⟨w, ⟨hw1, v, hv⟩, rfl⟩
  refine ⟨by positivity, ⟨w, by ring⟩, ?_⟩
  have hv' : v ^ 2 = 4 * (8 ^ 3 + (8 : ℤ)) * (2 * w) ^ 2 - 8 * (8 ^ 3 - 8 * 8) := by
    rw [show (4 * (8 ^ 3 + (8 : ℤ))) = 2080 by norm_num,
        show (8 * (8 ^ 3 - 8 * (8 : ℤ))) = 3584 by norm_num]; linear_combination hv
  have hpos : 0 < (2 * w) ^ 6 + 8 := by positivity
  exact sum2sq_x6_add (f := 8) (u := 8) (x := 2 * w) (v := v)
    (by norm_num) (⟨22, 6, by norm_num⟩) hpos hv'
/-- For `f = 5` and `u = 2`: there are infinitely many even `x ≥ 0` with `x⁶ + 5 ∈ S₂`. -/
lemma even_pow6_add5_S2_infinite :
    {x : ℤ | 0 ≤ x ∧ Even x ∧ Sum2Sq (x ^ 6 + 5)}.Infinite := by
  have hinf := genPell_infinite (a := 208) (c := 64)
    (by norm_num) (by native_decide) (by norm_num) 3 44 (by norm_num)
  refine (image_infinite_of_inj (f := fun w => 2 * w)
    (fun a b h => by simpa using h) hinf).mono ?_
  rintro _ ⟨w, ⟨hw1, v, hv⟩, rfl⟩
  refine ⟨by positivity, ⟨w, by ring⟩, ?_⟩
  have hv' : v ^ 2 = 4 * (2 ^ 3 + (5 : ℤ)) * (2 * w) ^ 2 - 2 * (2 ^ 3 - 8 * 5) := by
    rw [show (4 * (2 ^ 3 + (5 : ℤ))) = 52 by norm_num,
        show (2 * (2 ^ 3 - 8 * (5 : ℤ))) = -64 by norm_num]; linear_combination hv
  have hpos : 0 < (2 * w) ^ 6 + 5 := by positivity
  exact sum2sq_x6_add (f := 5) (u := 2) (x := 2 * w) (v := v)
    (by norm_num) (⟨3, 2, by norm_num⟩) hpos hv'
/-- For `f = -3` and `u = 2`: there are infinitely many even `x ≥ 0` with `x⁶ − 3 ∈ S₂`. -/
lemma even_pow6_sub3_S2_infinite :
    {x : ℤ | 0 ≤ x ∧ Even x ∧ Sum2Sq (x ^ 6 - 3)}.Infinite := by
  have hinf := genPell_infinite (a := 80) (c := -64)
    (by norm_num) (by native_decide) (by norm_num) 1 4 (by norm_num)
  refine (image_infinite_of_inj (f := fun w => 2 * w)
    (fun a b h => by simpa using h) hinf).mono ?_
  rintro _ ⟨w, ⟨hw1, v, hv⟩, rfl⟩
  have hw2pos : (0 : ℤ) < w ^ 2 := by nlinarith [sq_nonneg v, hv]
  have hw2 : (1 : ℤ) ≤ w ^ 2 := by omega
  refine ⟨by positivity, ⟨w, by ring⟩, ?_⟩
  have hv' : v ^ 2 = 4 * (2 ^ 3 + (-3 : ℤ)) * (2 * w) ^ 2 - 2 * (2 ^ 3 - 8 * (-3)) := by
    rw [show (4 * (2 ^ 3 + (-3 : ℤ))) = 20 by norm_num,
        show (2 * (2 ^ 3 - 8 * (-3 : ℤ))) = 64 by norm_num]; linear_combination hv
  have hpos : 0 < (2 * w) ^ 6 - 3 := by
    have h6 : (1 : ℤ) ≤ w ^ 6 := by
      have := one_le_pow₀ (n := 3) hw2
      nlinarith [this]
    have he : (2 * w) ^ 6 = 64 * w ^ 6 := by ring
    rw [he]; nlinarith [h6]
  have hpos' : 0 < (2 * w) ^ 6 + (-3 : ℤ) := by linarith
  have := sum2sq_x6_add (f := -3) (u := 2) (x := 2 * w) (v := v)
    (by norm_num) (⟨2, 1, by norm_num⟩) hpos' hv'
  rw [sub_eq_add_neg]; exact this
/-! ## Section 3: the main propositions -/
/-- **Proposition 3.1.** The equation `y² + x³y + z² + 1 = 0` (equation (2)) has
infinitely many integer solutions. -/
theorem prop_3_1 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0)
  refine odd_pow6_sub4_S2_infinite.mono ?_
  rintro x ⟨hodd, hS⟩
  exact sol_31 hodd hS
/-- **Proposition 3.2, equation (14).** `y² + x³y + z² − 2 = 0` has infinitely many
integer solutions. -/
theorem prop_3_2_eq14 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0)
  refine even_pow6_add8_S2_infinite.mono ?_
  rintro x ⟨_, hx, hS⟩
  exact sol_14 hx hS
/-- **Proposition 3.2, equation (15).** `y² + x³y + z² + z − 1 = 0` has infinitely many
integer solutions. -/
theorem prop_3_2_eq15 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0)
  refine even_pow6_add5_S2_infinite.mono ?_
  rintro x ⟨_, hx, hS⟩
  exact sol_15 hx hS
/-- **Proposition 3.2, equation (16).** `y² + x³y + z² + z + 1 = 0` has infinitely many
integer solutions. -/
theorem prop_3_2_eq16 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0)
  refine even_pow6_sub3_S2_infinite.mono ?_
  rintro x ⟨_, hx, hS⟩
  exact sol_16 hx hS
/-- **Proposition 3.2, equation (17).** `y² + x³y + y + z² + 1 = 0` has infinitely many
integer solutions.  Here we substitute `x = -w²` with `w` even, using
`(x³+1)²-4 = (w⁶-3)(w⁶+1)` and the fact that `w⁶-3 ∈ S₂` infinitely often. -/
theorem prop_3_2_eq17 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1 = 0)
  -- map `w ↦ -w²` (injective on nonnegatives) from the even `w` with `w⁶-3 ∈ S₂`.
  have himg : ((fun w : ℤ => -w ^ 2) '' {x : ℤ | 0 ≤ x ∧ Even x ∧ Sum2Sq (x ^ 6 - 3)}).Infinite := by
    refine even_pow6_sub3_S2_infinite.image ?_
    rintro a ⟨ha, _, _⟩ b ⟨hb, _, _⟩ hab
    have hab2 : a ^ 2 = b ^ 2 := by simpa using hab
    nlinarith [hab2, sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb]
  refine himg.mono ?_
  rintro _ ⟨w, ⟨hw0, hwe, hwS⟩, rfl⟩
  -- Sum2Sq ((-w²)³+1)²-4) since it equals (w⁶-3)(w⁶+1)
  have hS : Sum2Sq (((-w ^ 2) ^ 3 + 1) ^ 2 - 4) := by
    have hfac : ((-w ^ 2) ^ 3 + 1) ^ 2 - 4 = (w ^ 6 - 3) * (w ^ 6 + 1) := by ring
    rw [hfac]
    exact Sum2Sq.mul hwS ⟨w ^ 3, 1, by ring⟩
  have hxe : Even (-w ^ 2) := by
    obtain ⟨k, hk⟩ := hwe; exact ⟨-(2 * k ^ 2), by rw [hk]; ring⟩
  exact sol_17 hxe hS
/-! ## Section 4: general binary quadratic forms -/
/-- **Proposition 4.1** (the tangent construction for a general binary quadratic form
`F(y,z) = A y² + B y z + C z²`), algebraic core.  Let `m = F(p,q)`, `r = R'(u)`,
`s = Q(x) − u`, and `D = Du(Q(x))` the second-order Taylor coefficient.  If the tangent
direction `(λ, μ)` satisfies the line condition `2Apλ + B(pμ+qλ) + 2Cqμ = r` and
`F(λ,μ) = D`, then the point `(p + sλ, q + sμ)` on the line represents
`R(u+s) = m + sr + s²D`, i.e. `F(y,z) = R(Q(x))`. -/
lemma prop_4_1_core {A B C : ℤ} (p q m r s D lam mu : ℤ)
    (hm : m = A * p ^ 2 + B * p * q + C * q ^ 2)
    (hline : 2 * A * p * lam + B * (p * mu + q * lam) + 2 * C * q * mu = r)
    (hF : A * lam ^ 2 + B * lam * mu + C * mu ^ 2 = D) :
    A * (p + s * lam) ^ 2 + B * (p + s * lam) * (q + s * mu) + C * (q + s * mu) ^ 2
      = m + s * r + s ^ 2 * D := by
  subst hm hF; linear_combination s * hline
/-- **Proposition 4.4(a).** `2y² + yz + 2z² = x³ + 1` has infinitely many integer
solutions.  Explicit family: `x = 30n² + 15n + 1`, `y = 30n³ + 45n² + 15n + 1`,
`z = −(120n³ + 90n² + 15n)`. -/
theorem prop_4_4a :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 + 1}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => 2 * y ^ 2 + y * z + 2 * z ^ 2 = x ^ 3 + 1)
  have hinj : Function.Injective (fun n : ℕ => (30 * (n : ℤ) ^ 2 + 15 * n + 1)) := by
    intro a b h
    have : (a : ℤ) = b := by nlinarith [h, Nat.cast_nonneg (α := ℤ) a, Nat.cast_nonneg (α := ℤ) b]
    exact_mod_cast this
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨30 * (n : ℤ) ^ 3 + 45 * n ^ 2 + 15 * n + 1, -(120 * (n : ℤ) ^ 3 + 90 * n ^ 2 + 15 * n), ?_⟩
  ring
/-- **Proposition 4.4(b).** `2y² + yz + 2z² = x³ − 1` has infinitely many integer
solutions.  Explicit family: `x = 570n² + 225n + 24`, with `y, z` given by the tangent
construction. -/
theorem prop_4_4b :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 - 1}.Infinite := by
  apply infinite_triples_of_infinite_fst (R := fun x y z => 2 * y ^ 2 + y * z + 2 * z ^ 2 = x ^ 3 - 1)
  have hinj : Function.Injective (fun n : ℕ => (570 * (n : ℤ) ^ 2 + 225 * n + 24)) := by
    intro a b h
    have : (a : ℤ) = b := by nlinarith [h, Nat.cast_nonneg (α := ℤ) a, Nat.cast_nonneg (α := ℤ) b]
    exact_mod_cast this
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨3 + (570 * (n : ℤ) ^ 2 + 225 * n + 17) * (4 + 17 * n),
    12 + (570 * (n : ℤ) ^ 2 + 225 * n + 17) * (1 - 8 * n), ?_⟩
  ring
/-! ## Section 4: general infinitude and congruence machinery
This section formalises the remaining components of Section 4 of the paper: the full
infinitude statement of Proposition 4.1, Proposition 4.2 (solvability of the auxiliary
equation subject to congruences), and the two algorithms (Algorithm 2.2 for the sum of
two squares and Algorithm 4.3 for general non-degenerate forms), stated as theorems whose
hypotheses record the data produced by the corresponding search steps. -/
/-
If a set of integer pairs is infinite but each fibre over the first coordinate is
finite, then the set of first coordinates is infinite.
-/
lemma infinite_fst_of_finite_fibers {S : Set (ℤ × ℤ)} (hS : S.Infinite)
    (hfib : ∀ x : ℤ, {v : ℤ | (x, v) ∈ S}.Finite) :
    {x : ℤ | ∃ v : ℤ, (x, v) ∈ S}.Infinite := by
  exact fun h => hS <| Set.Finite.subset ( h.biUnion fun x _ => hfib x |> Set.Finite.image fun y => ( x, y ) ) fun x hx => by aesop;
/-
For `D ≠ 0`, the solution set of `D · v² = K` is finite.
-/
lemma finite_setOf_mul_sq_eq {D K : ℤ} (hD : D ≠ 0) : {v : ℤ | D * v ^ 2 = K}.Finite := by
  by_contra h_inf;
  exact h_inf <| Set.Finite.subset ( Set.finite_Icc ( - |K| ) |K| ) fun x hx => ⟨ by cases abs_cases K <;> cases lt_or_gt_of_ne hD <;> nlinarith [ hx.symm, sq_nonneg x ], by cases abs_cases K <;> cases lt_or_gt_of_ne hD <;> nlinarith [ hx.symm, sq_nonneg x ] ⟩
/-
The per-solution tangent construction of Proposition 4.1: for a single pair `(x, v)`
satisfying the auxiliary equation (27) and the congruences (28), the equation
`F(y,z) = R(Q(x))` has an integer solution `(y, z)` given by the tangent-line formula.
-/
lemma prop_4_1_solution {A B C : ℤ} (u p q r : ℤ) (R Q Du : ℤ → ℤ) (x v : ℤ)
    (hm : R u = A * p ^ 2 + B * p * q + C * q ^ 2) (hmne : R u ≠ 0)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (h27 : 4 * R u * Du (Q x) - r ^ 2 = -(B ^ 2 - 4 * A * C) * v ^ 2)
    (hdiv1 : (2 * |R u|) ∣ (r * p + v * (B * p + 2 * C * q)))
    (hdiv2 : (2 * |R u|) ∣ (r * q - v * (2 * A * p + B * q))) :
    ∃ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = R (Q x) := by
  have hlam : ∃ lam : ℤ, r * p + v * (B * p + 2 * C * q) = 2 * R u * lam := by
    cases abs_cases ( R u ) <;> [ exact dvd_trans ( by norm_num [ ‹_› ] ) hdiv1; exact dvd_trans ( by norm_num [ ‹_› ] ) hdiv1 ]
  obtain ⟨lam, hlam⟩ := hlam
  have hmu : ∃ mu : ℤ, r * q - v * (2 * A * p + B * q) = 2 * R u * mu := by
    cases abs_cases ( R u ) <;> [ exact dvd_trans ( by norm_num [ ‹_› ] ) hdiv2; exact dvd_trans ( by norm_num [ ‹_› ] ) hdiv2 ]
  obtain ⟨mu, hmu⟩ := hmu
  use p + (Q x - u) * lam, q + (Q x - u) * mu;
  refine mul_left_cancel₀ (pow_ne_zero 2 hmne) ?_
  -- Cancel a further factor `4` so the divisibility relations `hlam`, `hmu`
  -- (which carry a factor `2 * R u`) can be substituted without division.
  refine mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num) ?_
  linear_combination
      (-2*(Q x - u)*(R u)*(2*A*p+B*q) - 2*(Q x - u)^2*A*(r*p+v*(B*p+2*C*q))
        - (Q x - u)^2*B*(r*q-v*(2*A*p+B*q))
        + (Q x - u)^2*A*((r*p+v*(B*p+2*C*q)) - 2*R u*lam)
        + (Q x - u)^2*B*((r*q-v*(2*A*p+B*q)) - 2*R u*mu)) * hlam
    + (-2*(Q x - u)*(R u)*(B*p+2*C*q) - (Q x - u)^2*B*(r*p+v*(B*p+2*C*q))
        - 2*(Q x - u)^2*C*(r*q-v*(2*A*p+B*q))
        + (Q x - u)^2*C*((r*q-v*(2*A*p+B*q)) - 2*R u*mu)) * hmu
    + (-(Q x - u)^2*(A*p^2+B*p*q+C*q^2)) * h27
    + (-(4*(R u)^2 + 4*(Q x - u)*r*(R u) + 4*(Q x - u)^2*(R u)*Du (Q x))) * hm
    + (-4*(R u)^2) * (hTaylor (Q x))
/-
**Proposition 4.1.**  Let `F(y,z) = A y² + B y z + C z²` be non-degenerate
(`Δ = B² − 4AC ≠ 0`), let `m = R(u) = F(p,q) ≠ 0`, `r = R'(u)`, and let `Du` be the
second-order Taylor coefficient of `R` at `u`.  If the auxiliary equation (27),
`4 m · Du(Q(x)) − r² = −Δ v²`, together with the congruences (28) has infinitely many
integer solutions `(x, v)`, then `F(y,z) = R(Q(x))` is solvable for infinitely many `x`.
-/
theorem prop_4_1 {A B C : ℤ} (u p q r : ℤ) (R Q Du : ℤ → ℤ)
    (hΔ : B ^ 2 - 4 * A * C ≠ 0)
    (hm : R u = A * p ^ 2 + B * p * q + C * q ^ 2) (hmne : R u ≠ 0)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (hInf : {xv : ℤ × ℤ |
        4 * R u * Du (Q xv.1) - r ^ 2 = -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
        (2 * |R u|) ∣ (r * p + xv.2 * (B * p + 2 * C * q)) ∧
        (2 * |R u|) ∣ (r * q - xv.2 * (2 * A * p + B * q))}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = R (Q x)}.Infinite := by
  convert Set.Infinite.mono _ ( infinite_fst_of_finite_fibers hInf _ ) using 1;
  · exact fun x hx => by obtain ⟨ v, hv ⟩ := hx; exact prop_4_1_solution u p q r R Q Du x v hm hmne hTaylor hv.1 hv.2.1 hv.2.2;
  · intro x;
    refine' Set.Finite.subset ( finite_setOf_mul_sq_eq hΔ ) _;
    exacts [ r ^ 2 - 4 * R u * Du ( Q x ), fun v hv => by linear_combination' hv.1 ]
/-
**Proposition 4.2.**  Consider the auxiliary equation (30) `a x² + b x + c = −D v²`
(where `D = Δ` is the discriminant of the form) together with a congruence condition `cg`
on `v` that is periodic with period `2m` (`m ≠ 0`).  If (a) `a = 0` or `a(−D)` is a positive
non-square, (b) the discriminant `b² − 4ac ≠ 0`, and (c) there is one solution `(x₀, v₀)`
with `cg v₀`, then the equation has infinitely many integer solutions `(x, v)` with `cg v`.
(As in the paper, these are exactly conditions (a)–(c); the non-degeneracy `Δ ≠ 0` of the
form, a standing assumption of Section 4, is not needed for this infinitude statement.) -/
theorem prop_4_2 {a b c D m : ℤ} (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < a * (-D) ∧ ¬ IsSquare (a * (-D))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (cg : ℤ → Prop) (hperiod : ∀ v w : ℤ, cg v → cg (v + 2 * m * w))
    (x0 v0 : ℤ) (hsol : a * x0 ^ 2 + b * x0 + c = -D * v0 ^ 2) (hc0 : cg v0) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + b * p.1 + c = -D * p.2 ^ 2 ∧ cg p.2}.Infinite := by
  by_cases ha0 : a = 0;
  · refine Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun k : ℤ => ( x0 - 4 * D * m * k * ( v0 + m * b * k ), v0 + 2 * m * b * k ) ) from ?_ ) fun k => ⟨ ?_, ?_ ⟩ <;> simp_all +decide [ Function.Injective ];
    · linear_combination hsol;
    · simpa [ mul_assoc ] using hperiod v0 ( b * k ) hc0;
  · obtain ⟨ha_pos, ha_not_square⟩ := ha.resolve_left ha0;
    -- Set a' := 4*a*(-D), c' := b^2-4*a*c, X0 := 2*a*x0+b, M := |4*a*m| (note M > 0 since a ≠ 0, m ≠ 0).
    set a' := 4 * a * (-D)
    set c' := b ^ 2 - 4 * a * c
    set X0 := 2 * a * x0 + b
    set M := |4 * a * m| with hM_def
    have hM_pos : 0 < M := by
      exact abs_pos.mpr ( mul_ne_zero ( mul_ne_zero four_ne_zero ha0 ) hm );
    -- Apply `genPell_infinite_cong` to get P'.Infinite where P' = {p | p.2^2 = a'*p.1^2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}.
    have hP'_infinite : {p : ℤ × ℤ | p.2 ^ 2 = a' * p.1 ^ 2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}.Infinite := by
      apply genPell_infinite_cong;
      · grind;
      · simp +zetaDelta at *;
        rintro ⟨ k, hk ⟩;
        exact ha_not_square ⟨ k / 2, by cases abs_cases k <;> nlinarith [ Int.ediv_mul_cancel ( show 2 ∣ k from even_iff_two_dvd.mp ( by simpa +decide [ parity_simps ] using congr_arg Even hk ) ) ] ⟩;
      · grind +splitImp;
      · exact hM_pos;
      · grind;
    -- Show that the set of second coordinates of P' is infinite.
    have hVset_infinite : {W : ℤ | ∃ X : ℤ, (W, X) ∈ {p : ℤ × ℤ | p.2 ^ 2 = a' * p.1 ^ 2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}}.Infinite := by
      apply infinite_fst_of_finite_fibers hP'_infinite;
      intro x; exact Set.Finite.subset ( Set.finite_Icc ( - ( |a' * x ^ 2 + c'| ) ) ( |a' * x ^ 2 + c'| ) ) fun v hv => ⟨ by cases abs_cases ( a' * x ^ 2 + c' ) <;> nlinarith [ hv.1 ], by cases abs_cases ( a' * x ^ 2 + c' ) <;> nlinarith [ hv.1 ] ⟩ ;
    -- For W ∈ Vset, pick X with (W,X) ∈ P': from X ≡ X0 [ZMOD M] and 2*a ∣ M we get X ≡ X0 ≡ b [ZMOD 2*a], so 2*a ∣ (X - b); write X = 2*a*x + b.
    have hW_to_x : ∀ W ∈ {W : ℤ | ∃ X : ℤ, (W, X) ∈ {p : ℤ × ℤ | p.2 ^ 2 = a' * p.1 ^ 2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}}, ∃ x : ℤ, a * x ^ 2 + b * x + c = -D * W ^ 2 := by
      rintro W ⟨ X, hX ⟩;
      -- From X ≡ X0 [ZMOD M] and 2*a ∣ M we get X ≡ X0 ≡ b [ZMOD 2*a], so 2*a ∣ (X - b); write X = 2*a*x + b.
      obtain ⟨x, hx⟩ : ∃ x : ℤ, X = 2 * a * x + b := by
        have hX_mod : X ≡ X0 [ZMOD 2 * a] := by
          exact hX.2.2.of_dvd <| by exact ⟨ 2 * m * ( if 4 * a * m ≥ 0 then 1 else -1 ), by split_ifs <;> cases abs_cases ( 4 * a * m ) <;> linarith ⟩ ;
        obtain ⟨ k, hk ⟩ := hX_mod.symm.dvd;
        exact ⟨ k + x0, by linear_combination hk ⟩;
      simp +zetaDelta at *;
      exact ⟨ x, by rw [ hx ] at hX; cases lt_or_gt_of_ne ha0 <;> nlinarith ⟩;
    -- For W ∈ Vset, pick X with (W,X) ∈ P': from W ≡ v0 [ZMOD M] and 2*m ∣ M we get W ≡ v0 [ZMOD 2*m], so W = v0 + 2*m*t for some t, giving cg W by hperiod.
    have hW_to_cg : ∀ W ∈ {W : ℤ | ∃ X : ℤ, (W, X) ∈ {p : ℤ × ℤ | p.2 ^ 2 = a' * p.1 ^ 2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}}, cg W := by
      intros W hW
      obtain ⟨X, hX⟩ := hW
      have hW_mod : W ≡ v0 [ZMOD 2 * m] := by
        exact hX.2.1.of_dvd <| by exact ⟨ 2 * a * ( if 4 * a * m ≥ 0 then 1 else -1 ), by split_ifs <;> cases abs_cases ( 4 * a * m ) <;> nlinarith ⟩ ;
      obtain ⟨ k, hk ⟩ := hW_mod.symm.dvd;
      simpa [ sub_eq_iff_eq_add'.mp hk ] using hperiod v0 k hc0;
    intro H;
    exact hVset_infinite <| Set.Finite.subset ( H.image Prod.snd ) fun x hx => by obtain ⟨ y, hy ⟩ := hW_to_x x hx; exact ⟨ ( y, x ), ⟨ by linarith [ hy ], hW_to_cg x hx ⟩, rfl ⟩ ;
/-
**Algorithm 4.3** (stated as a theorem).  Given the data `(u, p, q)` with
`R(u) = F(p,q) ≠ 0` found in Step 1, the auxiliary equation written in the form (30) with
coefficients `(a, b, c)` (Step 2), and the verification of conditions (a)–(c) of
Proposition 4.2 (Step 3), the equation `F(y,z) = R(Q(x))` is solvable for infinitely many
integers `x`.  This is the composition of Proposition 4.2 and Proposition 4.1.
-/
theorem algorithm_4_3 {A B C : ℤ} (u p q r a b c : ℤ) (R Q Du : ℤ → ℤ)
    (hΔ : B ^ 2 - 4 * A * C ≠ 0)
    (hm : R u = A * p ^ 2 + B * p * q + C * q ^ 2) (hmne : R u ≠ 0)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (haux : ∀ x, 4 * R u * Du (Q x) - r ^ 2 = a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < a * (-(B ^ 2 - 4 * A * C)) ∧ ¬ IsSquare (a * (-(B ^ 2 - 4 * A * C)))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (x0 v0 : ℤ) (hsol : a * x0 ^ 2 + b * x0 + c = -(B ^ 2 - 4 * A * C) * v0 ^ 2)
    (hcong1 : (2 * |R u|) ∣ (r * p + v0 * (B * p + 2 * C * q)))
    (hcong2 : (2 * |R u|) ∣ (r * q - v0 * (2 * A * p + B * q))) :
    {x : ℤ | ∃ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = R (Q x)}.Infinite := by
  convert prop_4_1 u p q r R Q Du hΔ hm hmne hTaylor _;
  convert prop_4_2 ( show R u ≠ 0 by assumption ) ha hb _ _ x0 v0 _ _ using 1;
  rotate_left;
  use fun v => 2 * |R u| ∣ r * p + v * ( B * p + 2 * C * q ) ∧ 2 * |R u| ∣ r * q - v * ( 2 * A * p + B * q );
  · intro v w hvw
    have h2 : (2 : ℤ) * |R u| ∣ 2 * R u :=
      ⟨if R u > 0 then 1 else -1, by split_ifs <;> cases abs_cases (R u) <;> linarith⟩
    refine ⟨?_, ?_⟩
    · have hkey : r * p + (v + 2 * R u * w) * (B * p + 2 * C * q)
          = (r * p + v * (B * p + 2 * C * q)) + 2 * R u * (w * (B * p + 2 * C * q)) := by ring
      rw [hkey]
      exact dvd_add hvw.1 (h2.mul_right (w * (B * p + 2 * C * q)))
    · have hkey : r * q - (v + 2 * R u * w) * (2 * A * p + B * q)
          = (r * q - v * (2 * A * p + B * q)) - 2 * R u * (w * (2 * A * p + B * q)) := by ring
      rw [hkey]
      exact dvd_sub hvw.2 (h2.mul_right (w * (2 * A * p + B * q)))
  · exact hsol;
  · exact ⟨ hcong1, hcong2 ⟩;
  · simp +decide only [haux]
/-
The per-solution identity of Algorithm 2.2 (sum-of-two-squares case): if `R(u)` is a
positive sum of two squares and the auxiliary equation `4 R(u) Du(Q(x)) − r² = v²` holds,
then `R(Q(x))` is a sum of two squares.  Uses identity (7) and property (*).
-/
lemma sum2sq_of_aux (u r : ℤ) (R Q Du : ℤ → ℤ) (x v : ℤ)
    (hRuS : Sum2Sq (R u)) (hRupos : 0 < R u)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (hv : 4 * R u * Du (Q x) - r ^ 2 = v ^ 2) :
    Sum2Sq (R (Q x)) := by
  -- From key, `Sum2Sq (4 * (R u) * (R (Q x)))` holds.
  have h_key : Sum2Sq (4 * (R u) * (R (Q x))) := by
    -- From key, `Sum2Sq (4 * (R u) * (R (Q x)))` holds via ⟨2*(R u)+r*(Q x - u), (Q x - u)*v, key⟩.
    use 2 * R u + r * (Q x - u), (Q x - u) * v;
    grind;
  by_cases hRQx : R ( Q x ) > 0;
  · convert Sum2Sq.div ( show 0 < 4 * R u by linarith ) hRQx _ h_key using 1;
    exact Sum2Sq.mul ( by exact ⟨ 2, 0, by ring ⟩ ) hRuS;
  · exact ⟨ 0, 0, by nlinarith [ show 0 ≤ 4 * R u * R ( Q x ) by obtain ⟨ a, b, h ⟩ := h_key; nlinarith ] ⟩
/-
**Algorithm 2.2** (stated as a theorem).  For the sum-of-two-squares form, given
`R(u) ∈ S₂` positive (Step 1) and the auxiliary equation (10) `a x² + b x + c = v²`
satisfying conditions (a)–(c) (Steps 2–3), `R(Q(x))` is a sum of two squares for infinitely
many integers `x`.
-/
theorem algorithm_2_2 (u r a b c : ℤ) (R Q Du : ℤ → ℤ)
    (hRuS : Sum2Sq (R u)) (hRupos : 0 < R u)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (haux : ∀ x, 4 * R u * Du (Q x) - r ^ 2 = a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (x0 v0 : ℤ) (hsol : a * x0 ^ 2 + b * x0 + c = v0 ^ 2) :
    {x : ℤ | Sum2Sq (R (Q x))}.Infinite := by
  rcases ha with rfl | ⟨ ha, ha' ⟩;
  · -- Since $b \neq 0$, the equation $b * x + c = v^2$ has infinitely many solutions for $x$.
    have h_inf_solutions : ∀ k : ℤ, Sum2Sq (R (Q (x0 + 2 * v0 * k + b * k ^ 2))) := by
      intro k
      have hv : 4 * R u * Du (Q (x0 + 2 * v0 * k + b * k ^ 2)) - r ^ 2 = (v0 + b * k) ^ 2 := by
        grind
      exact sum2sq_of_aux u r R Q Du (x0 + 2 * v0 * k + b * k ^ 2) (v0 + b * k) hRuS hRupos hTaylor hv;
    by_contra h_contra;
    -- Since $b \neq 0$, the set $\{x0 + 2 * v0 * k + b * k ^ 2 \mid k \in \mathbb{Z}\}$ is infinite.
    have h_infinite_set : Set.Infinite {x : ℤ | ∃ k : ℤ, x = x0 + 2 * v0 * k + b * k ^ 2} := by
      by_cases hb_pos : 0 < b;
      · refine Set.infinite_of_forall_exists_gt ?_;
        exact fun n => ⟨ _, ⟨ |n - x0| + |2 * v0| + 1, rfl ⟩, by cases abs_cases ( n - x0 ) <;> cases abs_cases ( 2 * v0 ) <;> nlinarith ⟩;
      · by_cases hb_neg : b < 0;
        · refine Set.infinite_of_not_bddBelow ?_;
          norm_num [ bddBelow_def ];
          exact fun x => ⟨ |x - x0| + |2 * v0| + 1, by cases abs_cases ( x - x0 ) <;> cases abs_cases ( 2 * v0 ) <;> nlinarith ⟩;
        · interval_cases b ; norm_num at hb;
    exact h_contra <| h_infinite_set.mono fun x hx => by obtain ⟨ k, rfl ⟩ := hx; exact h_inf_solutions k;
  · set a' := 4 * a
    set c' := b^2 - 4 * a * c
    set X0 := 2 * a * x0 + b
    set M := 2 * a
    have ha'_pos : 0 < a' := by
      positivity
    have ha'_not_square : ¬ IsSquare a' := by
      simp +zetaDelta at *;
      exact fun ⟨ k, hk ⟩ => ha' ⟨ k / 2, by cases abs_cases k <;> nlinarith [ Int.ediv_mul_cancel ( show 2 ∣ k from even_iff_two_dvd.mp ( by simpa +decide [ parity_simps ] using congr_arg Even hk ) ) ] ⟩
    have hc'_ne_zero : c' ≠ 0 := by
      exact hb
    have hX0 : X0^2 = a' * v0^2 + c' := by
      linear_combination' hsol * 4 * a
    have hM_pos : 0 < M := by
      exact mul_pos zero_lt_two ha
    have hM : |M| = M := by
      exact abs_of_pos hM_pos
    have hPell : {p : ℤ × ℤ | p.2^2 = a' * p.1^2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}.Infinite := by
      apply genPell_infinite_cong ha'_pos ha'_not_square hc'_ne_zero M hM_pos v0 X0 hX0
    generalize_proofs at *;
    -- Let $Vset$ be the set of first coordinates $W$ of these solutions.
    set Vset := {W : ℤ | ∃ X : ℤ, (W, X) ∈ {p : ℤ × ℤ | p.2^2 = a' * p.1^2 + c' ∧ p.1 ≡ v0 [ZMOD M] ∧ p.2 ≡ X0 [ZMOD M]}} with hVset_def
    have hVset_inf : Vset.Infinite := by
      intro hVset_finite
      generalize_proofs at *;
      refine hPell <| Set.Finite.subset ( hVset_finite.prod <| Set.Finite.biUnion hVset_finite fun x hx => Set.finite_Ico ( - ( |a' * x ^ 2 + c'| ) ) ( |a' * x ^ 2 + c'| + 1 ) ) ?_;
      simp +contextual [ Set.subset_def ];
      exact fun a b hb ha hb' => ⟨ ⟨ b, hb, ha, hb' ⟩, a, by cases abs_cases ( a' * a ^ 2 + c' ) <;> nlinarith, ⟨ b, hb, ha, hb' ⟩, by cases abs_cases ( a' * a ^ 2 + c' ) <;> nlinarith ⟩
    generalize_proofs at *;
    -- For each $W \in Vset$, there exists $x$ such that $a * x^2 + b * x + c = W^2$.
    have h_exists_x : ∀ W ∈ Vset, ∃ x : ℤ, a * x^2 + b * x + c = W^2 := by
      intro W hW
      obtain ⟨X, hX⟩ := hW
      have hX_eq : X^2 = a' * W^2 + c' := by
        exact hX.1
      have hX_mod : X ≡ X0 [ZMOD M] := by
        exact hX.2.2
      have hX_div : (2 * a) ∣ (X - b) := by
        have := hX_mod.symm.dvd; obtain ⟨ k, hk ⟩ := this; exact ⟨ k + x0, by linarith ⟩ ;
      obtain ⟨k, hk⟩ : ∃ k : ℤ, X = 2 * a * k + b := by
        exact ⟨ hX_div.choose, eq_add_of_sub_eq hX_div.choose_spec ⟩
      generalize_proofs at *;
      exact ⟨ k, by subst hk; nlinarith ⟩
    generalize_proofs at *;
    -- For each $W \in Vset$, there exists $x$ such that $R(Q(x))$ is a sum of two squares.
    have h_sum2sq : ∀ W ∈ Vset, ∃ x : ℤ, Sum2Sq (R (Q x)) ∧ a * x^2 + b * x + c = W^2 := by
      intros W hW
      obtain ⟨x, hx⟩ := h_exists_x W hW
      use x
      generalize_proofs at *;
      exact ⟨ sum2sq_of_aux u r R Q Du x W hRuS hRupos hTaylor ( by linarith [ haux x ] ), hx ⟩
    generalize_proofs at *;
    contrapose! hVset_inf;
    refine Set.Finite.subset ( hVset_inf.biUnion fun x hx => Set.finite_Icc ( - ( |a * x ^ 2 + b * x + c| ) ) ( |a * x ^ 2 + b * x + c| ) ) ?_;
    intro W hW; obtain ⟨ x, hx₁, hx₂ ⟩ := h_sum2sq W hW; exact Set.mem_iUnion₂.mpr ⟨ x, hx₁, by constructor <;> cases abs_cases ( a * x ^ 2 + b * x + c ) <;> nlinarith ⟩ ;
/-! ## Section 4: non-multiplicativity of `2y² + yz + 2z²`
The algorithm of Section 4 works for every non-degenerate binary quadratic form, in
particular without any multiplicativity assumption.  Here we record the paper's running
example of a form that is *not* multiplicative: `F(y,z) = 2y² + yz + 2z²` represents the
positive integer `2` (as `F(0,1)`) but does not represent `2·2 = 4`. -/
/-- A binary quadratic form `F : ℤ → ℤ → ℤ` is *multiplicative* if, whenever it represents
two positive integers `m` and `n`, it also represents their product `m · n`. -/
def MultiplicativeForm (F : ℤ → ℤ → ℤ) : Prop :=
  ∀ m n : ℤ, 0 < m → 0 < n →
    (∃ y z, F y z = m) → (∃ y z, F y z = n) → ∃ y z, F y z = m * n
/-- `2y² + yz + 2z²` represents `2`, since `F(0,1) = 2`. -/
lemma form2_represents_two : ∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 2 :=
  ⟨0, 1, by ring⟩
/-
`2y² + yz + 2z²` does not represent `4`: the equation `2y² + yz + 2z² = 4` has no
integer solutions.
-/
lemma form2_not_represents_four : ¬ ∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 4 := by
  simp only [not_exists]
  intro x y H
  have hx1 : x ≤ 2 := by nlinarith [sq_nonneg (x + y)]
  have hx2 : -2 ≤ x := by nlinarith [sq_nonneg (x + y)]
  have hy1 : y ≤ 2 := by nlinarith [sq_nonneg (x + y)]
  have hy2 : -2 ≤ y := by nlinarith [sq_nonneg (x + y)]
  interval_cases x <;> interval_cases y <;> omega
/-
**Non-multiplicativity of `2y² + yz + 2z²`** (Section 4).  The form represents the
positive integer `2` but not `2·2 = 4`, hence it is not multiplicative.
-/
theorem form2_not_multiplicative :
    ¬ MultiplicativeForm (fun y z : ℤ => 2 * y ^ 2 + y * z + 2 * z ^ 2) := by
  intro h;
  convert form2_not_represents_four <| h 2 2 ( by norm_num ) ( by norm_num ) form2_represents_two form2_represents_two
/-! ## Section 4: the degenerate case `Δ = 0`
When the discriminant `Δ = B² − 4AC` of the form `F(y,z) = A y² + B y z + C z²` vanishes,
the form is, up to an integer factor, the square of a linear form:
`(A,B,C) = (k n², 2 k n m, k m²)` and `F(y,z) = k (n y + m z)²`.  Consequently any equation
`F(y,z) = P(x)` reduces to `k t² = P(x)` with `t = n y + m z`, and it has infinitely many
integer solutions iff the reduced equation has a solution whose `t`-coordinate is divisible
by `gcd(n,m)`. -/
/-
**Degenerate form factorisation** (Section 4).  A binary quadratic form with vanishing
discriminant `B² − 4AC = 0` is an integer multiple of the square of a linear form: there
exist integers `k, n, m` with `A = k n²`, `B = 2 k n m`, `C = k m²`.
-/
lemma degenerate_factorization {A B C : ℤ} (hΔ : B ^ 2 - 4 * A * C = 0) :
    ∃ k n m : ℤ, A = k * n ^ 2 ∧ B = 2 * k * n * m ∧ C = k * m ^ 2 := by
  rcases eq_or_ne A 0 with ( rfl | hA ) <;> rcases eq_or_ne C 0 with ( rfl | hC );
  · exact ⟨ 0, 0, 0, by norm_num, by norm_num; nlinarith, by norm_num ⟩;
  · exact ⟨ C, 0, 1, by ring, by nlinarith, by ring ⟩;
  · exact ⟨ A, 1, 0, by norm_num, by norm_num; nlinarith, by norm_num ⟩;
  · -- Let $g = \gcd(A, C)$, then $A = gA_1$ and $C = gC_1$ where $\gcd(A_1, C_1) = 1$.
    obtain ⟨g, A1, C1, hg, hA1, hC1⟩ : ∃ g A1 C1 : ℤ, A = g * A1 ∧ C = g * C1 ∧ Int.gcd A1 C1 = 1 := by
      exact ⟨ Int.gcd A C, A / Int.gcd A C, C / Int.gcd A C, by rw [ Int.mul_ediv_cancel' ( Int.gcd_dvd_left _ _ ) ], by rw [ Int.mul_ediv_cancel' ( Int.gcd_dvd_right _ _ ) ], by rw [ Int.gcd_div ( Int.gcd_dvd_left _ _ ) ( Int.gcd_dvd_right _ _ ), Int.natAbs_natCast, Nat.div_self ( Int.gcd_pos_of_ne_zero_left _ hA ) ] ⟩;
    -- From $B^2 = 4AC$, we get $B^2 = 4g^2A_1C_1$, so $B = 2gb_1$ for some integer $b_1$.
    obtain ⟨b1, hb1⟩ : ∃ b1 : ℤ, B = 2 * g * b1 := by
      exact Int.pow_dvd_pow_iff two_ne_zero |>.1 ⟨ A1 * C1, by subst_vars; linarith ⟩;
    -- From $b1^2 = A1C1$, we know that $A1$ and $C1$ are both perfect squares or both negative perfect squares.
    obtain ⟨n, m, hn, hm⟩ : ∃ n m : ℤ, A1 = n^2 ∧ C1 = m^2 ∨ A1 = -n^2 ∧ C1 = -m^2 := by
      have h_sq : b1^2 = A1 * C1 := by
        exact mul_left_cancel₀ ( show g ^ 2 ≠ 0 by aesop ) ( by subst_vars; linarith );
      -- Since $A1$ and $C1$ are coprime and their product is a perfect square, each must be a perfect square.
      have h_sq_A1 : ∃ n : ℤ, A1 = n^2 ∨ A1 = -n^2 := by
        have h_perfect_square : ∃ n : ℕ, A1.natAbs = n^2 := by
          exact exists_eq_pow_of_mul_eq_pow ( by aesop ) ( by rw [ ← Int.natAbs_mul ] ; simpa [ Int.natAbs_pow ] using congr_arg Int.natAbs h_sq.symm );
        exact Exists.elim h_perfect_square fun n hn => ⟨ n, eq_or_eq_neg_of_abs_eq ( by linarith ) ⟩
      have h_sq_C1 : ∃ m : ℤ, C1 = m^2 ∨ C1 = -m^2 := by
        rcases h_sq_A1 with ⟨ n, rfl | rfl ⟩;
        · -- Since $n^2 \mid b1^2$, we have $n \mid b1$. Let $b1 = kn$ for some integer $k$.
          obtain ⟨k, hk⟩ : ∃ k : ℤ, b1 = n * k := by
            exact Int.pow_dvd_pow_iff ( by decide ) |>.1 ( h_sq.symm ▸ dvd_mul_right _ _ );
          exact ⟨ k, Or.inl <| mul_left_cancel₀ ( pow_ne_zero 2 <| show n ≠ 0 by aesop_cat ) <| by subst hk; linarith ⟩;
        · by_cases hn : n = 0;
          · grind;
          · exact ⟨ b1 / n, Or.inr <| by cases lt_or_gt_of_ne hn <;> nlinarith [ sq_nonneg <| b1 / n - n, Int.ediv_mul_cancel <| show n ∣ b1 from Int.pow_dvd_pow_iff two_ne_zero |>.1 <| by exact ⟨ -C1, by linarith ⟩ ] ⟩;
      rcases h_sq_A1 with ⟨ n, hn | hn ⟩ <;> rcases h_sq_C1 with ⟨ m, hm | hm ⟩ <;> simp_all +decide;
      · exact ⟨ n, m, Or.inl ⟨ rfl, rfl ⟩ ⟩;
      · nlinarith [ mul_self_pos.2 hA.2, mul_self_pos.2 hC ];
      · nlinarith [ mul_self_pos.2 hA.2, mul_self_pos.2 hC ];
      · exact ⟨ n, m, Or.inr ⟨ rfl, rfl ⟩ ⟩;
    · -- From $b1^2 = A1C1$, we know that $b1 = \pm nm$.
      have hb1_cases : b1 = n * m ∨ b1 = -n * m := by
        simp_all +decide [ mul_pow ];
        exact eq_or_eq_neg_of_sq_eq_sq _ _ <| mul_left_cancel₀ ( pow_ne_zero 2 hA.1 ) <| by linarith;
      rcases hb1_cases with ( rfl | rfl ) <;> simp_all +decide [ mul_assoc ];
      · exact ⟨ g, n, rfl, m, rfl, rfl ⟩;
      · exact ⟨ g, n, rfl, -m, by ring, by ring ⟩;
    · -- From $b1^2 = A1C1$, we know that $b1 = \pm nm$.
      have hb1_cases : b1 = n * m ∨ b1 = -n * m := by
        simp_all +decide [ mul_pow ];
        exact eq_or_eq_neg_of_sq_eq_sq _ _ <| mul_left_cancel₀ ( pow_ne_zero 2 hA.1 ) <| by linarith;
      cases' hb1_cases with hb1_cases hb1_cases <;> simp_all +decide [ mul_assoc ];
      · exact ⟨ -g, n, by ring, -m, by ring, by ring ⟩;
      · exact ⟨ -g, n, by ring, m, by ring, by ring ⟩
/-- Given the degenerate factorisation, the form collapses to `k (n y + m z)²`. -/
lemma degenerate_reduces {A B C k n m : ℤ}
    (hA : A = k * n ^ 2) (hB : B = 2 * k * n * m) (hC : C = k * m ^ 2) (y z : ℤ) :
    A * y ^ 2 + B * y * z + C * z ^ 2 = k * (n * y + m * z) ^ 2 := by
  subst hA hB hC; ring
/-
**Degenerate case, infinitude criterion** (Section 4, eq. (33)).  If the linear form
`(n, m)` is non-trivial, then `k (n y + m z)² = P(x)` has infinitely many integer solutions
`(x, y, z)` if and only if the reduced equation `k t² = P(x)` has a solution `(x₀, t₀)` with
`t₀` divisible by `gcd(n, m)`.
-/
theorem degenerate_infinite_iff {k n m : ℤ} (hnm : ¬ (n = 0 ∧ m = 0)) (P : ℤ → ℤ) :
    {p : ℤ × ℤ × ℤ | k * (n * p.2.1 + m * p.2.2) ^ 2 = P p.1}.Infinite
      ↔ ∃ x0 t0 : ℤ, k * t0 ^ 2 = P x0 ∧ (Int.gcd n m : ℤ) ∣ t0 := by
  constructor;
  · intro h_inf
    obtain ⟨p, hp⟩ : ∃ p : ℤ × ℤ × ℤ, k * (n * p.2.1 + m * p.2.2) ^ 2 = P p.1 := by
      exact h_inf.nonempty;
    exact ⟨ p.1, n * p.2.1 + m * p.2.2, hp, Int.dvd_add ( dvd_mul_of_dvd_left ( Int.gcd_dvd_left _ _ ) _ ) ( dvd_mul_of_dvd_left ( Int.gcd_dvd_right _ _ ) _ ) ⟩;
  · rintro ⟨ x0, t0, ht0, h ⟩;
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, n * a + m * b = Int.gcd n m := by
      exact Int.gcd_eq_gcd_ab n m ▸ ⟨ _, _, rfl ⟩;
    -- Let $g = \gcd(n, m)$ and write $t0 = g * s$ for some integer $s$.
    obtain ⟨s, hs⟩ : ∃ s : ℤ, t0 = Int.gcd n m * s := h
    set g := Int.gcd n m with hg
    have hg_pos : 0 < g := by
      exact Nat.pos_of_ne_zero ( mt Int.gcd_eq_zero_iff.mp hnm )
    have hn' : n = g * (n / g) := by
      rw [ mul_comm, Int.ediv_mul_cancel ( Int.gcd_dvd_left _ _ ) ]
    have hm' : m = g * (m / g) := by
      rw [ Int.mul_ediv_cancel' ( Int.gcd_dvd_right _ _ ) ]
    have hn'm' : Int.gcd (n / g) (m / g) = 1 := by
      rw [ Int.gcd_div ( Int.gcd_dvd_left _ _ ) ( Int.gcd_dvd_right _ _ ), Int.natAbs_natCast, Nat.div_self hg_pos ]
    have hnm' : n / g * a + m / g * b = 1 := by
      exact mul_left_cancel₀ ( Nat.cast_ne_zero.mpr hg_pos.ne' ) ( by linear_combination' hab - hn' * a - hm' * b );
    -- Define the function $f : ℤ → ℤ × ℤ × ℤ$ by $f(w) = (x0, y0 + m' * w, z0 - n' * w)$.
    set f : ℤ → ℤ × ℤ × ℤ := fun w => (x0, a * s + (m / g) * w, b * s - (n / g) * w) with hf_def
    have hf_mem : ∀ w : ℤ, f w ∈ {p : ℤ × ℤ × ℤ | k * (n * p.2.1 + m * p.2.2) ^ 2 = P p.1} := by
      grind +qlia
    have hf_inj : Function.Injective f := by
      norm_num [ Function.Injective ];
      grind +qlia
    exact Set.infinite_of_injective_forall_mem hf_inj hf_mem
/-- **The degenerate case `Δ = 0`** (Section 4), stated for the form `A y² + B y z + C z²`.
Combining the factorisation with the infinitude criterion: with factorisation data
`(k, n, m)` and non-trivial linear part `(n, m)`, the equation `F(y,z) = P(x)` has
infinitely many integer solutions iff the reduced equation `k t² = P(x)` has a solution
whose `t`-coordinate is divisible by `gcd(n, m)`. -/
theorem degenerate_case {A B C k n m : ℤ}
    (hA : A = k * n ^ 2) (hB : B = 2 * k * n * m) (hC : C = k * m ^ 2)
    (hnm : ¬ (n = 0 ∧ m = 0)) (P : ℤ → ℤ) :
    {p : ℤ × ℤ × ℤ | A * p.2.1 ^ 2 + B * p.2.1 * p.2.2 + C * p.2.2 ^ 2 = P p.1}.Infinite
      ↔ ∃ x0 t0 : ℤ, k * t0 ^ 2 = P x0 ∧ (Int.gcd n m : ℤ) ∣ t0 := by
  have hset : {p : ℤ × ℤ × ℤ | A * p.2.1 ^ 2 + B * p.2.1 * p.2.2 + C * p.2.2 ^ 2 = P p.1}
      = {p : ℤ × ℤ × ℤ | k * (n * p.2.1 + m * p.2.2) ^ 2 = P p.1} := by
    ext p
    simp only [Set.mem_setOf_eq, degenerate_reduces hA hB hC]
  rw [hset, degenerate_infinite_iff hnm P]
end SumSquaresPaper
