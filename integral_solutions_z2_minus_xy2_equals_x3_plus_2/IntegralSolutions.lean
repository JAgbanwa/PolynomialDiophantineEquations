import Mathlib
/- ======================= (from Defs.lean) ======================= -/
/-!
# Integral solutions of `z² - x·y² = x³ + 2`
This project formalises the paper *"Integral solutions of `z² - xy² = x³ + 2`"*, which
gives a complete and effective classification of the integer solutions of the equation
  `z² - x·y² = x³ + 2`,  `(x, y, z) ∈ ℤ³`.
This file collects the basic definitions used throughout: the solution predicate `IsSol`,
and the set `A` of admissible positive `x` values.
-/
namespace CubicNorm
/-- The Diophantine equation under study: `z² - x·y² = x³ + 2`.
Equivalently `z² - x·y² - x³ - 2 = 0`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 - x * y ^ 2 = x ^ 3 + 2
/-- The set `A` from (1.2): positive odd integers all of whose prime divisors are
`≡ 1` or `7 (mod 8)`.  The integer `1` belongs to `A` vacuously. -/
def InA (n : ℤ) : Prop :=
  0 < n ∧ Odd n ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → p % 8 = 1 ∨ p % 8 = 7
end CubicNorm
/- ======================= (from NonPositive.lean) ======================= -/
/-!
# The nonpositive case (Lemma 2.1 / Theorem 1.1(i))
The only solutions of `z² - x·y² = x³ + 2` with `x ≤ 0` are the four triples
`(-1, 0, 1), (-1, 0, -1), (-1, 1, 0), (-1, -1, 0)`.
-/
namespace CubicNorm
/-
**Lemma 2.1 / Theorem 1.1(i).** Complete list of solutions with `x ≤ 0`.
-/
theorem classification_nonpos (x y z : ℤ) (hx : x ≤ 0) :
    IsSol x y z ↔
      (x = -1 ∧ y = 0 ∧ z = 1) ∨ (x = -1 ∧ y = 0 ∧ z = -1) ∨
      (x = -1 ∧ y = 1 ∧ z = 0) ∨ (x = -1 ∧ y = -1 ∧ z = 0) := by
  constructor;
  · intro hxy
    have h_bound : -1 ≤ x ∧ x ≤ 0 := by
      constructor <;> nlinarith [ sq_nonneg ( x + 1 ), sq_nonneg y, sq_nonneg z, hxy.symm ];
    cases h_bound ; interval_cases x <;> simp_all +decide [ IsSol ];
    · have : y ≤ 1 := Int.le_of_lt_add_one ( by nlinarith ) ; ( have : y ≥ -1 := Int.le_of_lt_add_one ( by nlinarith ) ; interval_cases y <;> ( have : z ≤ 1 := Int.le_of_lt_add_one ( by nlinarith ) ; ( have : z ≥ -1 := Int.le_of_lt_add_one ( by nlinarith ) ; interval_cases z <;> trivial; ) ) );
    · nlinarith [ show z ≤ 1 by nlinarith, show z ≥ -1 by nlinarith ];
  · rintro ( ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ ) <;> trivial
end CubicNorm
/- ======================= (from ParamRestrict.lean) ======================= -/
/-!
# Restrictions on the parameter `x` (Section 2)
If `(x, y, z)` is a solution with `x > 0`, then `x` is odd and lies in `A`
(Proposition 2.3).  In particular, no positive even value of `x` occurs.
The only quadratic-residue input is Lemma 2.2: if `r² ≡ 2 (mod p)` for an odd prime `p`,
then `p ≡ 1` or `7 (mod 8)`.  We obtain this from Mathlib's `ZMod.exists_sq_eq_two_iff`.
-/
namespace CubicNorm
/-- **Lemma 2.2.** If `2` is a quadratic residue modulo an odd prime `p`,
then `p ≡ 1` or `7 (mod 8)`. -/
theorem prime_of_two_residue (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : ∃ r : ℤ, (r ^ 2 - 2) % (p : ℤ) = 0) : p % 8 = 1 ∨ p % 8 = 7 := by
  haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_iff_eq_add ] ;
  obtain ⟨ r, hr ⟩ := h; have := ZMod.exists_sq_eq_two_iff ( p := p ) ; simp_all +decide ;
  exact this.mp ⟨ r, by rw [ ← hr, sq ] ⟩
/-
A positive odd integer all of whose prime divisors are `≡ 1` or `7 (mod 8)`
is itself `≡ 1` or `7 (mod 8)`.  (Multiplicativity of the class `{1, 7}` in `(ℤ/8)ˣ`.)
-/
theorem odd_mod8_of_primes (n : ℕ) (hn : Odd n)
    (h : ∀ p, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 7) :
    n % 8 = 1 ∨ n % 8 = 7 := by
  rw [ ← Nat.prod_primeFactorsList hn.pos.ne' ];
  have h_prod_mod : ∀ {l : List ℕ}, (∀ p ∈ l, p % 8 = 1 ∨ p % 8 = 7) → (List.prod l) % 8 = 1 ∨ (List.prod l) % 8 = 7 := by
    intro l hl; induction l <;> norm_num at *;
    rcases ‹ ( ∀ p ∈ _, p % 8 = 1 ∨ p % 8 = 7 ) → _› hl.2 with h | h <;> rcases hl.1 with h' | h' <;> norm_num [ Nat.mul_mod, h, h' ];
  exact h_prod_mod fun p hp => h p ( Nat.prime_of_mem_primeFactorsList hp ) ( Nat.dvd_of_mem_primeFactorsList hp )
/-
From a solution, `x ∣ z² - 2`, since `z² - 2 = x·(x² + y²)`.
-/
theorem dvd_sq_sub_two (x y z : ℤ) (h : IsSol x y z) : x ∣ z ^ 2 - 2 := by
  exact ⟨ x ^ 2 + y ^ 2, by linarith [ h.symm ] ⟩
/-
Every positive solution value of `x` is odd (no positive even `x` occurs).
-/
theorem pos_x_odd (x y z : ℤ) (h : IsSol x y z) (hx : 0 < x) : Odd x := by
  by_cases h_even : Even x <;> simp_all +decide [ IsSol ];
  -- If $x$ is even but not divisible by 4, then $x = 2m$ with $m$ odd.
  obtain ⟨m, rfl, hm⟩ : ∃ m : ℤ, x = 2 * m ∧ Odd m := by
    obtain ⟨ m, rfl ⟩ := h_even; use m; ring_nf at *; simp_all +decide [ parity_simps ] ;
    rcases Int.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf at * <;> have := congr_arg ( · % 4 ) h <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at this ⊢;
    rcases Int.even_or_odd' z with ⟨ k, rfl | rfl ⟩ <;> ring_nf at this <;> norm_num at this;
  -- From $z^2 = 8m^3 + 2my^2 + 2$, we get $z^2 \equiv 2m + 10 \pmod{16}$.
  have h_mod16 : z^2 % 16 = (2 * m + 10) % 16 := by
    -- Since $y$ is odd, we have $y^2 \equiv 1 \pmod{8}$.
    have hy_sq_mod8 : y^2 % 8 = 1 := by
      by_cases hy_even : Even y <;> simp_all +decide [ Int.even_iff ];
      · obtain ⟨ k, rfl ⟩ := hy_even; ring_nf at h ⊢; have := congr_arg ( · % 4 ) h; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, sq ] at this; have := Int.emod_nonneg z four_pos.ne'; have := Int.emod_lt_of_pos z four_pos; interval_cases z % 4 <;> norm_num at *;
      · rw [ ← Int.emod_add_mul_ediv y 2, hy_even ] ; ring_nf; norm_num [ Int.add_emod, Int.mul_emod ] ;
        norm_num [ sq, Int.mul_emod ] ; have := Int.emod_nonneg ( y / 2 ) ( by decide : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos ( y / 2 ) ( by decide : ( 0 : ℤ ) < 8 ) ; interval_cases y / 2 % 8 <;> trivial;
    -- Write `y^2 = 8*(y^2/8) + 1` (from `y^2 ≡ 1 (mod 8)`) and `m = 2*k+1` (from `Odd m`),
    -- then exhibit `z^2` explicitly as `16*W + (4*k+12)`; `omega` finishes from that witness.
    have hY : y ^ 2 = 8 * (y ^ 2 / 8) + 1 := by omega
    obtain ⟨ k, rfl ⟩ := hm
    obtain ⟨ W, hW ⟩ : ∃ W : ℤ, z ^ 2 = 16 * W + (4 * k + 12) :=
      ⟨ 4 * k ^ 3 + 6 * k ^ 2 + 3 * k + (2 * k + 1) * (y ^ 2 / 8),
        by linear_combination h + 2 * (2 * k + 1) * hY ⟩
    omega
  -- Since $m$ is odd, we have $m \equiv 3$ or $5 \pmod{8}$.
  have h_mod8 : m % 8 = 3 ∨ m % 8 = 5 := by
    obtain ⟨ k, rfl ⟩ := hm; ring_nf at *; norm_num [ Int.add_emod, Int.mul_emod ] at *;
    rw [ ← Int.emod_emod_of_dvd k ( by decide : ( 8 : ℤ ) ∣ 16 ) ] ; have := Int.emod_nonneg k ( by decide : ( 16 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos k ( by decide : ( 0 : ℤ ) < 16 ) ; interval_cases k % 16 <;> norm_num at *;
    all_goals rw [ sq, Int.mul_emod ] at h_mod16; have := Int.emod_nonneg z ( by decide : ( 16 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos z ( by decide : ( 0 : ℤ ) < 16 ) ; interval_cases z % 16 <;> contradiction;
  -- Since $m$ is odd, we have $m \equiv 3$ or $5 \pmod{8}$, and thus $m \equiv 3$ or $5 \pmod{8}$, contradicting `odd_mod8_of_primes`.
  have h_contradiction : ∀ p : ℕ, p.Prime → p ∣ Int.natAbs m → p % 8 = 1 ∨ p % 8 = 7 := by
    intros p hp hp_div
    have h_div_z : (p : ℤ) ∣ z^2 - 2 := by
      exact dvd_trans ( Int.natCast_dvd.mpr hp_div ) ( by use 8 * m ^ 2 + 2 * y ^ 2; linarith );
    apply prime_of_two_residue p hp (by
    rintro rfl; omega;) (by
    exact ⟨ z, Int.emod_eq_zero_of_dvd h_div_z ⟩);
  have := odd_mod8_of_primes ( Int.natAbs m ) ( by simpa using hm ) h_contradiction; omega;
/-
Every odd prime divisor of a positive solution value of `x` is `≡ 1` or `7 (mod 8)`.
-/
theorem pos_x_primes (x y z : ℤ) (h : IsSol x y z) (hodd : Odd x) :
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → p % 8 = 1 ∨ p % 8 = 7 := by
  -- Let p be prime with (p:ℤ) ∣ x. First, p ≠ 2: if p = 2 then 2 ∣ x, contradicting `Odd x` (hodd). So p is odd, p ≠ 2.
  intro p hp hpx
  by_cases hp2 : p = 2;
  · simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
    grind +qlia;
  · -- Now z² ≡ 2 (mod p): from `dvd_sq_sub_two x y z h` we have x ∣ z² - 2, and (p:ℤ) ∣ x, so (p:ℤ) ∣ z² - 2 by dvd_trans.
    have h_mod : (z ^ 2 - 2) % p = 0 := by
      exact Int.emod_eq_zero_of_dvd <| dvd_trans hpx <| dvd_sq_sub_two x y z h;
    exact prime_of_two_residue p hp hp2 ⟨ z, h_mod ⟩
/-- **Proposition 2.3.** If `(x, y, z)` is a solution with `x > 0`, then `x ∈ A`
(in particular `x` is odd and no positive even value of `x` occurs). -/
theorem pos_x_in_A (x y z : ℤ) (h : IsSol x y z) (hx : 0 < x) : InA x := by
  refine ⟨hx, pos_x_odd x y z h hx, ?_⟩
  exact pos_x_primes x y z h (pos_x_odd x y z h hx)
end CubicNorm
/- ======================= (from SquareCase.lean) ======================= -/
/-!
# The positive square case (Proposition 3.1)
We classify the solutions of `z² - x·y² = x³ + 2` for which `x = m²` is a positive square.
The paper phrases the answer via the positive divisors `d` of `Nₘ = m⁶ + 2` satisfying
`d < √Nₘ` and `Nₘ/d ≡ d (mod 2m)`, with `Yₘ,d = (Nₘ/d - d)/(2m)`, `Zₘ,d = (Nₘ/d + d)/2`.
Writing `d = |z| - m|y|` and `e = |z| + m|y| = Nₘ/d`, this is exactly the same as saying the
solution corresponds to a factorization `Nₘ = d·e` with `2m|y| = e - d` and `2|z| = e + d`.
We state Proposition 3.1 in this equivalent factorization form, which avoids integer division.
-/
namespace CubicNorm
/-
**Proposition 3.1** (factorization form). For a positive integer `m`, the triple
`(m², y, z)` is a solution iff `|z| - m|y|` and `|z| + m|y|` give a factorization
`d · e = m⁶ + 2` of `Nₘ`, equivalently there is a factorization `d·e = m⁶ + 2` with
`0 < d`, `2m|y| = e - d` and `2|z| = e + d`.
-/
theorem square_case (m : ℤ) (hm : 0 < m) (y z : ℤ) :
    IsSol (m ^ 2) y z ↔
      ∃ d e : ℤ, 0 < d ∧ d * e = m ^ 6 + 2 ∧ 2 * m * |y| = e - d ∧ 2 * |z| = e + d := by
  constructor <;> intro h;
  · unfold IsSol at h;
    refine ⟨ |z| - m * |y|, |z| + m * |y|, ?_, ?_, by ring, by ring ⟩
    · cases abs_cases z <;> cases abs_cases y <;> push_cast [ * ] <;> nlinarith [ pow_pos hm 3 ];
    · have hzy : (|z| - m * |y|) * (|z| + m * |y|) = z ^ 2 - m ^ 2 * y ^ 2 := by
        rw [← sq_abs z, ← sq_abs y]; ring
      rw [hzy]; linear_combination h
  · unfold IsSol;
    grind
end CubicNorm
/- ======================= (from Nonsquare.lean) ======================= -/
/-!
# The positive nonsquare case (Section 4)
For a positive nonsquare `D`, the equation `z² - x·y² = x³ + 2` with `x = D` becomes the
generalized Pell equation `z² - D·y² = D³ + 2 = N_D`.  Using the norm-one units of `ℤ[√D]`
(Pell units), the solutions split into finitely many orbits.
Here we prove:
* `exists_pos_pell_unit`: existence of a nontrivial Pell unit `(u, v)` with `u, v > 0`;
* `nonsquare_infinite` (Proposition 4.3 / Corollary 5.1(iv)): if there is *one* solution with
  `x = D` (nonsquare, positive), then there are infinitely many.
-/
namespace CubicNorm
/-- For a positive nonsquare `D`, there is a nontrivial Pell unit with positive coordinates:
`u² - D·v² = 1` with `u, v > 0`. -/
theorem exists_pos_pell_unit (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ u ^ 2 - D * v ^ 2 = 1 := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hD hns
  refine ⟨|x|, |y|, ?_, ?_, ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, zero_sub] at hxy
      nlinarith [sq_nonneg y, mul_nonneg hD.le (sq_nonneg y)]
    · positivity
  · positivity
  · rw [sq_abs, sq_abs]; exact hxy
/-
**Proposition 4.3 / Corollary 5.1(iv).** For a positive nonsquare `D`, if there is at least one
solution with `x = D`, then there are infinitely many.
-/
theorem nonsquare_infinite (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D)
    (y0 z0 : ℤ) (hsol : IsSol D y0 z0) :
    {p : ℤ × ℤ | IsSol D p.1 p.2}.Infinite := by
  -- Set N = D^3 + 2 > 0. From `hsol : IsSol D y0 z0` (i.e. z0^2 - D*y0^2 = D^3 + 2), set A0 = |z0|, B0 = |y0|. Then A0^2 - D*B0^2 = N (using sq_abs), A0 > 0 (since z0 ≠ 0: if z0 = 0 then -D*y0^2 = N > 0, impossible as D>0), and B0 ≥ 0.
  set N := D^3 + 2 with hN
  have hN_pos : 0 < N := by
    positivity
  set A0 := |z0| with hA0
  set B0 := |y0| with hB0
  have hA0_pos : 0 < A0 := by
    exact abs_pos.mpr ( show z0 ≠ 0 from by rintro rfl; exact absurd hsol ( by norm_num [ IsSol ] ; nlinarith [ pow_pos hD 3 ] ) )
  have hB0_nonneg : 0 ≤ B0 := by
    exact abs_nonneg _
  have hA0B0 : A0^2 - D * B0^2 = N := by
    aesop;
  -- Obtain a positive Pell unit via `exists_pos_pell_unit D hD hns`: u, v with 0<u, 0<v, u^2 - D*v^2 = 1.
  obtain ⟨u, v, hu_pos, hv_pos, huv⟩ : ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ u ^ 2 - D * v ^ 2 = 1 := by
    exact exists_pos_pell_unit D hD hns;
  -- Define a sequence `f : ℕ → ℤ × ℤ` by recursion:
  set f : ℕ → ℤ × ℤ := fun n => Nat.rec (A0, B0) (fun _ p => (u * p.1 + D * v * p.2, v * p.1 + u * p.2)) n with hf_def;
  have hf_seq : ∀ n, (f n).1 ^ 2 - D * (f n).2 ^ 2 = N := by
    intro n; induction n <;> simp_all +decide ; nlinarith;;
  have hf_pos : ∀ n, 0 < (f n).1 ∧ 0 ≤ (f n).2 := by
    exact fun n => Nat.recOn n ⟨ hA0_pos, hB0_nonneg ⟩ fun n ih => ⟨ by exact add_pos_of_pos_of_nonneg ( mul_pos hu_pos ih.1 ) ( mul_nonneg ( mul_nonneg hD.le hv_pos.le ) ih.2 ), by exact add_nonneg ( mul_nonneg hv_pos.le ih.1.le ) ( mul_nonneg hu_pos.le ih.2 ) ⟩ ;;
  have hf_mono : StrictMono (fun n => (f n).2) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n; nlinarith [ hf_pos n, mul_pos hu_pos hv_pos, mul_pos hu_pos ( hf_pos n |>.1 ), mul_pos hv_pos ( hf_pos n |>.1 ) ] ;;
  exact Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun n => ( ( f n |>.2 ), ( f n |>.1 ) ) ) from fun m n hmn => hf_mono.injective <| by aesop ) fun n => show IsSol D ( ( f n |>.2 ) ) ( ( f n |>.1 ) ) from by unfold IsSol; linarith [ hf_seq n ] ;
end CubicNorm
/- ======================= (from OrbitDecomposition.lean) ======================= -/
set_option maxHeartbeats 1000000
/-!
# Orbit decomposition for the generalized Pell equation (Proposition 4.2)
Let `D > 0` be nonsquare, `N > 0`, and let `(u, v)` be a positive Pell unit
(`u² - D·v² = 1`, `u, v > 0`), corresponding to the norm-one unit `ε = u + v·√D > 1`.
Multiplication by `ε` acts on the set of solutions `A² - D·B² = N` with `A > 0`, `B ≥ 0` by
  `stepF (A, B) = (u·A + D·v·B,  v·A + u·B)`.
Its inverse is `stepB (A, B) = (u·A - D·v·B,  u·B - v·A)`.
A solution `(A, B)` is a **reduced seed** when `u·B - v·A < 0` (equivalently, `ε⁻¹·(A,B)` leaves
the region `{A > 0, B ≥ 0}`; equivalently `√N ≤ A + B√D < ε·√N`).  We show:
* `orbit_reduce` (surjectivity of the orbit map): every solution is `stepF^[n]` of a reduced seed;
* `seeds_finite`: there are only finitely many reduced seeds, all with `B² < v²·N`
  (matching the paper's bound `0 ≤ B < v·√N`).
-/
namespace CubicNorm
/-- Multiplication by the Pell unit `ε = u + v√D` on coefficient pairs `(A, B)`. -/
def stepF (D u v : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (u * p.1 + D * v * p.2, v * p.1 + u * p.2)
/-
`stepF` preserves the norm `A² - D·B²`.
-/
theorem stepF_norm (D u v : ℤ) (huv : u ^ 2 - D * v ^ 2 = 1) (p : ℤ × ℤ) :
    (stepF D u v p).1 ^ 2 - D * (stepF D u v p).2 ^ 2 = p.1 ^ 2 - D * p.2 ^ 2 := by
  unfold stepF; linear_combination huv * ( p.1 ^ 2 - D * p.2 ^ 2 ) ;
/-- Iterating `stepF` preserves the norm `A² - D·B²`. -/
theorem stepF_iterate_norm (D u v : ℤ) (huv : u ^ 2 - D * v ^ 2 = 1) (n : ℕ) (p : ℤ × ℤ) :
    ((stepF D u v)^[n] p).1 ^ 2 - D * ((stepF D u v)^[n] p).2 ^ 2 = p.1 ^ 2 - D * p.2 ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stepF_norm D u v huv, ih]
/-
**Proposition 4.2 (surjectivity).** Every solution `(A, B)` with `A > 0`, `B ≥ 0` and
`A² - D·B² = N` is `stepF^[n]` of a reduced seed `(A₀, B₀)` (with `u·B₀ - v·A₀ < 0`).
-/
theorem orbit_reduce (D u v N : ℤ) (hD : 0 < D) (hu : 0 < u) (hv : 0 < v)
    (huv : u ^ 2 - D * v ^ 2 = 1) (hN : 0 < N)
    (A B : ℤ) (hA : 0 < A) (hB : 0 ≤ B) (hnorm : A ^ 2 - D * B ^ 2 = N) :
    ∃ (A0 B0 : ℤ) (n : ℕ), 0 < A0 ∧ 0 ≤ B0 ∧ A0 ^ 2 - D * B0 ^ 2 = N ∧
      u * B0 - v * A0 < 0 ∧ (A, B) = (stepF D u v)^[n] (A0, B0) := by
  induction' n : Int.toNat A using Nat.strong_induction_on with n ih generalizing A B; rcases lt_trichotomy ( u * B - v * A ) 0 with h | h | h <;> simp_all +decide ;
  · exact ⟨ A, hA, B, hB, hnorm, h, 0, rfl ⟩;
  · refine' ⟨ u * A - D * v * B, _, u * B - v * A, _, _, _, 1, _ ⟩ <;> norm_num [ stepF ];
    · nlinarith [ mul_pos hD hv ];
    · linarith;
    · grind;
    · nlinarith [ mul_pos hu hA, mul_pos hu hv, mul_pos hv hA, mul_pos hv hv, mul_pos hD hu, mul_pos hD hv, mul_pos hD hA, mul_pos hD hv ];
    · grind +qlia;
  · -- Let $A' = uA - DvB$ and $B' = uB - vA$.
    set A' := u * A - D * v * B
    set B' := u * B - v * A;
    -- We need to show that $A'$ and $B'$ satisfy the conditions.
    have hA' : 0 < A' := by
      nlinarith [ mul_pos hu hA, mul_pos hu hv, mul_pos hu hD, mul_pos hv hA, mul_pos hv hD, mul_pos hD hA ]
    have hB' : 0 ≤ B' := by
      exact sub_nonneg_of_le h.le
    have hnorm' : A' ^ 2 - D * B' ^ 2 = N := by
      grind +ring
    have hA'_lt_A : A' < A := by
      nlinarith [ mul_pos hu hA, mul_pos hv hA, mul_pos hu hv, mul_le_mul_of_nonneg_left h.le hD.le, mul_le_mul_of_nonneg_left h.le hu.le, mul_le_mul_of_nonneg_left h.le hv.le ];
    -- By the induction hypothesis, there exists a reduced seed $(A0, B0)$ and $m$ such that $(A', B') = (stepF D u v)^[m] (A0, B0)$.
    obtain ⟨A0, hA0_pos, B0, hB0_nonneg, hA0_norm, hA0_reduced, m, hm⟩ : ∃ A0 B0 m, 0 < A0 ∧ 0 ≤ B0 ∧ A0 ^ 2 - D * B0 ^ 2 = N ∧ u * B0 < v * A0 ∧ (A', B') = (stepF D u v)^[m] (A0, B0) := by
      grind +revert;
    use A0, hB0_nonneg, hA0_pos, hA0_norm, hA0_reduced, m, B0 + 1;
    simp_all +decide [ Function.iterate_succ_apply', stepF ];
    grind
/-
**Proposition 4.2 (finiteness).** The set of reduced seeds is finite; every reduced seed
satisfies `B² < v²·N` (the paper's bound `0 ≤ B < v·√N`).
-/
theorem seeds_finite (D u v N : ℤ) (hu : 0 < u) (hv : 0 < v)
    (huv : u ^ 2 - D * v ^ 2 = 1) :
    {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = N ∧ u * p.2 - v * p.1 < 0}.Finite := by
  -- By definition of $S$, we know that for any $(A, B) \in S$, $B^2 < v^2 \cdot N$.
  have h_bound : ∀ p : ℤ × ℤ, p ∈ {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1^2 - D * p.2^2 = N ∧ u * p.2 - v * p.1 < 0} → p.2^2 < v^2 * N := by
    simp +zetaDelta at *;
    intro a b ha hb hab huv';
    nlinarith [ mul_pos hu ( sub_pos.mpr huv' ), mul_pos hv ( sub_pos.mpr huv' ), mul_pos hu hv ];
  -- Since there are only finitely many integers $B$ such that $B^2 < v^2 \cdot N$, the set of possible $B$ values is finite.
  have h_B_finite : {B : ℤ | ∃ A : ℤ, 0 < A ∧ 0 ≤ B ∧ A^2 - D * B^2 = N ∧ u * B - v * A < 0}.Finite := by
    exact Set.Finite.subset ( Set.finite_Icc ( - ( v ^ 2 * N ) ) ( v ^ 2 * N ) ) fun x hx => ⟨ by nlinarith [ h_bound ( hx.choose, x ) ⟨ hx.choose_spec.1, hx.choose_spec.2.1, hx.choose_spec.2.2.1, hx.choose_spec.2.2.2 ⟩ ], by nlinarith [ h_bound ( hx.choose, x ) ⟨ hx.choose_spec.1, hx.choose_spec.2.1, hx.choose_spec.2.2.1, hx.choose_spec.2.2.2 ⟩ ] ⟩;
  refine Set.Finite.subset ( h_B_finite.biUnion fun B _ ↦ Set.finite_Icc ( 0 : ℤ ) ( N + D * B ^ 2 ) |> Set.Finite.image fun A ↦ ( A, B ) ) ?_;
  exact fun p hp => Set.mem_iUnion₂.mpr ⟨ p.2, ⟨ p.1, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2 ⟩, Set.mem_image_of_mem _ ⟨ by nlinarith [ hp.1, hp.2.1, hp.2.2.1 ], by nlinarith [ hp.1, hp.2.1, hp.2.2.1 ] ⟩ ⟩
end CubicNorm
/- ======================= (from InfiniteFamily.lean) ======================= -/
/-!
# An explicit infinite family (Corollary 5.2)
For `x = 23` the equation `z² - x·y² = x³ + 2` has infinitely many integer solutions,
coming from the Pell unit `24 + 5·√23`.  We define the sequence of pairs `(Yₙ, Zₙ)` by
  `(Y₀, Z₀) = (23, 156)`,  `Zₙ₊₁ = 24·Zₙ + 115·Yₙ`,  `Yₙ₊₁ = 5·Zₙ + 24·Yₙ`,
and show each `(23, ±Yₙ, ±Zₙ)` is a solution, and that they are pairwise distinct.
-/
namespace CubicNorm
/-- The sequence `n ↦ (Yₙ, Zₙ)` from Corollary 5.2, with `fst = Yₙ`, `snd = Zₙ`. -/
def seq23 : ℕ → ℤ × ℤ
  | 0 => (23, 156)
  | (n + 1) => (5 * (seq23 n).2 + 24 * (seq23 n).1, 24 * (seq23 n).2 + 115 * (seq23 n).1)
/-
Each pair in the sequence satisfies the norm equation `Zₙ² - 23·Yₙ² = 23³ + 2`.
-/
theorem seq23_isSol (n : ℕ) : IsSol 23 (seq23 n).1 (seq23 n).2 := by
  induction' n with n ih <;> unfold IsSol at * <;> simp_all +decide [ seq23 ];
  linarith
/-
The `Y`-coordinates are strictly increasing, hence the pairs are pairwise distinct.
-/
theorem seq23_Y_strictMono : StrictMono (fun n => (seq23 n).1) := by
  -- By induction, we can show that both coordinates are positive.
  have h_pos : ∀ n, 0 < (seq23 n).1 ∧ 0 < (seq23 n).2 := by
    intro n; induction n <;> simp_all +decide [ seq23 ] ;
    constructor <;> linarith;
  refine' strictMono_nat_of_lt_succ _;
  exact fun n => by erw [ show seq23 ( n + 1 ) = ( 5 * ( seq23 n |>.2 ) + 24 * ( seq23 n |>.1 ), 24 * ( seq23 n |>.2 ) + 115 * ( seq23 n |>.1 ) ) from rfl ] ; norm_num; linarith [ h_pos n ] ;
/-
**Corollary 5.2.** The equation has infinitely many integer solutions
(witnessed by `x = 23`).
-/
theorem infinitely_many_solutions :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Infinite := by
  -- Define the injection `g : ℕ → ℤ × ℤ × ℤ`, `g n = (23, (seq23 n).1, (seq23 n).2)`.
  set g : ℕ → ℤ × ℤ × ℤ := fun n => (23, (seq23 n).1, (seq23 n).2);
  -- Show that `g` is injective.
  have hg_inj : Function.Injective g := by
    norm_num [ Function.Injective, g ];
    exact fun n m h => by simpa using StrictMono.injective ( show StrictMono ( fun n => ( seq23 n |>.1 ) ) from seq23_Y_strictMono ) ( congr_arg Prod.fst h ) ;
  exact Set.infinite_of_injective_forall_mem hg_inj fun n => seq23_isSol n
end CubicNorm
/- ======================= (from Examples.lean) ======================= -/
/-!
# Worked examples (Example 3.2 and Remark 5.3)
Concrete instances from the paper:
* Example 3.2: `(1, ±1, ±2)` and `(49, ±2801, ±19610)` are solutions.
* Remark 5.3: `x = 7` lies in `A` but the equation has *no* solution with `x = 7`;
  so membership in `A` is necessary but not sufficient.
-/
namespace CubicNorm
/-- Example 3.2: `(1, 1, 2)` is a solution. -/
theorem example_x_one : IsSol 1 1 2 := by norm_num [IsSol]
/-- Example 3.2: `(49, 2801, 19610)` is a solution (`m = 7`, `x = m² = 49`). -/
theorem example_x_fortynine : IsSol 49 2801 19610 := by norm_num [IsSol]
/-- Example 5.4/5.5: `(23, 23, 156)` is a solution. -/
theorem example_x_twentythree : IsSol 23 23 156 := by norm_num [IsSol]
/-
`7 ∈ A`: it is odd and its only prime divisor `7 ≡ 7 (mod 8)`.
-/
theorem seven_mem_A : InA 7 := by
  exact ⟨ by decide, by decide, fun p hp h => by have := Int.le_of_dvd ( by decide ) h; have := ( show p ≤ 7 by exact_mod_cast this ) ; interval_cases p <;> trivial ⟩
/-
**Remark 5.3.** There is no solution with `x = 7`, even though `7 ∈ A`.
Hence membership in `A` is necessary but not sufficient.
-/
theorem no_sol_x_seven : ¬ ∃ y z : ℤ, IsSol 7 y z := by
  simp +zetaDelta at *;
  -- Assume there exist integers $y$ and $z$ such that $z^2 - 7*y^2 = 345$.
  intro y z h
  have h25 : (z : ZMod 25)^2 - 7*(y : ZMod 25)^2 = 20 := by
    have := congrArg ( fun t : ℤ => ( t : ZMod 25 ) ) h; push_cast at this ⊢; ring_nf at this ⊢; aesop;
  -- We need to show that there are no integers $y$ and $z$ such that $z^2 - 7y^2 = 345$.
  have h_no_solution : ∀ (y z : ZMod 25), y^2 - 7 * z^2 ≠ 20 := by
    decide;
  exact h_no_solution _ _ h25
end CubicNorm
/- ======================= (from Classification.lean) ======================= -/
/-!
# The complete classification (Theorem 1.1 and Corollary 5.1)
This file assembles the pieces proved in the other files into the complete classification of
integer solutions of `z² - x·y² = x³ + 2`, and records the case analysis of Corollary 5.1.
* Nonpositive `x`: `classification_nonpos` (four solutions, all with `x = -1`).
* Necessary condition: any positive solution value `x` lies in `A` (`pos_x_in_A`).
* Positive square `x = m²`: `square_case` (finite divisor/factorization description).
* Positive nonsquare `x = D`: `nonsquare_classification` (orbit description) and
  `nonsquare_infinite` (none or infinitely many).
-/
namespace CubicNorm
/-
**Complete nonsquare classification (Theorem 1.1(iii)).** Given a positive nonsquare `D`
and any positive Pell unit `(u, v)` (`u² - D·v² = 1`, `u, v > 0`), the triple `(D, y, z)` is a
solution iff `(|z|, |y|)` is obtained from a reduced seed `(A₀, B₀)` (with `u·B₀ - v·A₀ < 0`)
by `n` applications of the unit multiplication `stepF`.  Together with `seeds_finite` this shows
the solutions split into finitely many Pell orbits.
-/
theorem nonsquare_classification (D : ℤ) (hD : 0 < D)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (huv : u ^ 2 - D * v ^ 2 = 1)
    (y z : ℤ) :
    IsSol D y z ↔
      ∃ (A0 B0 : ℤ) (n : ℕ),
        0 < A0 ∧ 0 ≤ B0 ∧ A0 ^ 2 - D * B0 ^ 2 = D ^ 3 + 2 ∧ u * B0 - v * A0 < 0 ∧
        |z| = ((stepF D u v)^[n] (A0, B0)).1 ∧ |y| = ((stepF D u v)^[n] (A0, B0)).2 := by
  constructor <;> intro h;
  · convert orbit_reduce D u v ( D ^ 3 + 2 ) hD hu hv huv ( by positivity ) |z| |y| _ _ _ using 1;
    · simp +decide [ Prod.ext_iff ];
    · exact abs_pos.mpr ( show z ≠ 0 by rintro rfl; nlinarith [ h.symm, pow_pos hD 3 ] );
    · positivity;
    · rw [ sq_abs, sq_abs ]; exact h;
  · obtain ⟨ A0, B0, n, hA0, hB0, hA0B0, huv, hz, hy ⟩ := h; unfold IsSol; simp_all +decide ;
    convert stepF_iterate_norm D u v _ n ( A0, B0 ) using 1;
    · rw [ ← hz, ← hy, sq_abs, sq_abs ];
    · linarith;
    · assumption
/-! ### Corollary 5.1 (case analysis for fixed `x`) -/
/-
Corollary 5.1(i): there are no solutions with `x < -1`.
-/
theorem no_sol_of_x_lt_neg_one (x y z : ℤ) (hx : x < -1) : ¬ IsSol x y z := by
  exact fun h => by have := ( classification_nonpos x y z ( by linarith ) ) |>.1 h; omega;
/-
Corollary 5.1(i): there are no solutions with `x = 0`.
-/
theorem no_sol_of_x_eq_zero (y z : ℤ) : ¬ IsSol 0 y z := by
  intro h; unfold IsSol at h; nlinarith [ show z ≤ 1 by nlinarith, show z ≥ -1 by nlinarith ]
/-
Corollary 5.1(i): there are no solutions with `x > 0` even.
-/
theorem no_sol_of_pos_even (x y z : ℤ) (hx : 0 < x) (he : Even x) : ¬ IsSol x y z := by
  intro h; have := CubicNorm.pos_x_in_A x y z h hx; simp_all +decide [ InA ] ;
  exact absurd this.1 ( by simpa using he )
/-
Corollary 5.1(ii): for `x = -1` there are exactly four solutions.
-/
theorem solutions_x_neg_one :
    {p : ℤ × ℤ | IsSol (-1) p.1 p.2} = {(0, 1), (0, -1), (1, 0), (-1, 0)} := by
  refine' Set.ext fun p => _;
  constructor;
  · intro hp
    have := classification_nonpos (-1) p.1 p.2 (by norm_num)
    aesop;
  · rintro ( rfl | rfl | rfl | rfl ) <;> norm_num [ IsSol ]
/-
Corollary 5.1(iii): for a positive square `x = m²` there are finitely many solutions.
-/
theorem finite_solutions_of_pos_square (m : ℤ) (hm : 0 < m) :
    {p : ℤ × ℤ | IsSol (m ^ 2) p.1 p.2}.Finite := by
  -- By definition of $IsSol$, we know that $z^2 - m^2*y^2 = m^6 + 2$.
  have h_eq : ∀ p : ℤ × ℤ, IsSol (m ^ 2) p.1 p.2 → p.2 ^ 2 - m ^ 2 * p.1 ^ 2 = m ^ 6 + 2 := by
    intro p hp; unfold IsSol at hp; linear_combination hp
  -- Since $p.2^2 - m^2*p.1^2 = m^6 + 2$, we have $|p.2 - m*p.1| \leq m^6 + 2$ and $|p.2 + m*p.1| \leq m^6 + 2$.
  have h_bounds : ∀ p : ℤ × ℤ, IsSol (m ^ 2) p.1 p.2 → |p.2 - m * p.1| ≤ m ^ 6 + 2 ∧ |p.2 + m * p.1| ≤ m ^ 6 + 2 := by
    intros p hp
    have h_div : (p.2 - m * p.1) * (p.2 + m * p.1) = m ^ 6 + 2 := by
      linear_combination' h_eq p hp;
    exact ⟨ Int.le_of_dvd ( by positivity ) ( by rw [ ← h_div ] ; norm_num ), Int.le_of_dvd ( by positivity ) ( by rw [ ← h_div ] ; norm_num ) ⟩;
  refine Set.Finite.subset ( Set.Finite.prod ( Set.finite_Icc ( - ( m ^ 6 + 2 ) ) ( m ^ 6 + 2 ) ) ( Set.finite_Icc ( - ( m ^ 6 + 2 ) ) ( m ^ 6 + 2 ) ) ) ?_;
  intro p hp; specialize h_bounds p hp; constructor <;> constructor <;> nlinarith [ abs_le.mp h_bounds.1, abs_le.mp h_bounds.2 ] ;
end CubicNorm
/- ======================= (from Main.lean) ======================= -/
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
