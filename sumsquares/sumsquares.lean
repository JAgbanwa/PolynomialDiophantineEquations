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
* `sum2sq_x6_add`           : the core tangent identity: if the auxiliary Pell equation
                              is solvable then `x⁶ + f` is a sum of two squares.
* `prop_3_1`                : `y² + x³y + z² + 1 = 0` has infinitely many integer solutions.
* `prop_3_2_eq14/15/16/17`  : the four length-9 equations (14)–(17) each have infinitely
                              many integer solutions.
* `prop_4_1`                : the tangent construction for a general form (Proposition 4.1).
* `prop_4_4a`, `prop_4_4b`  : the equations `2y² + yz + 2z² = x³ ± 1` have infinitely many
                              integer solutions (Proposition 4.4).
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
lemma prop_4_1 {A B C : ℤ} (p q m r s D lam mu : ℤ)
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
end SumSquaresPaper
