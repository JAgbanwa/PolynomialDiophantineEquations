import Mathlib
open scoped BigOperators
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# Infinitely many integer solutions of `y² + x³y + z² + 1 = 0`
This file formalises the paper *"Infinitely Many Integer Solutions of
`y² + x³y + z² + 1 = 0`"*.
The proof has three ingredients:
1. **Reduction** (`reduction`): completing the square reduces the construction of
   solutions to representing `n⁶ - 4` as a sum of two integer squares, for `n` odd.
2. **A rational two–square construction** (`tangent_identity`): a tangent-plane
   identity on `A² + B² = u³ - 4`, together with an explicit generalized Pell
   equation, gives infinitely many odd integers `N` for which `N⁶ - 4` is a sum of
   two *rational* squares.
3. **Rational to integral** (`rat_to_int`): the two-squares theorem converts the
   rational representations into integer representations.
-/
namespace Diophantine
/-! ## Part 1 : the reduction lemma -/
/-
**Lemma 1.1.** If `n` is odd and `n⁶ - 4 = a² + b²` for integers `a, b`, then the
equation `y² + n³y + z² + 1 = 0` has an integer solution.
-/
lemma reduction (n a b : ℤ) (hodd : Odd n) (hab : n ^ 6 - 4 = a ^ 2 + b ^ 2) :
    ∃ y z : ℤ, y ^ 2 + n ^ 3 * y + z ^ 2 + 1 = 0 := by
  obtain ⟨ k, rfl ⟩ : ∃ k, n = 2 * k + 1 := hodd;
  -- Since $a$ and $b$ have opposite parity, we can assume without loss of generality that $a$ is odd and $b$ is even.
  by_cases ha_odd : Odd a;
  · -- Since $a$ is odd, we can write $a = 2m + 1$ for some integer $m$.
    obtain ⟨ m, rfl ⟩ : ∃ m, a = 2 * m + 1 := ha_odd;
    obtain ⟨ z, rfl ⟩ := even_iff_two_dvd.mp ( show Even b from by replace hab := congr_arg ( · % 4 ) hab ; rcases Int.even_or_odd' b with ⟨ c, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at * );
    exact ⟨ m - k * ( 4 * k ^ 2 + 6 * k + 3 ), z, by linarith ⟩;
  · -- Since $a$ is even and $b$ is odd, we can set $b - (2k + 1)^3 = 2y$ and $a = 2z$.
    obtain ⟨ y, hy ⟩ : ∃ y, b - (2 * k + 1) ^ 3 = 2 * y := by
      exact even_iff_two_dvd.mp ( by apply_fun Even at *; simp_all +decide [ parity_simps ] )
    obtain ⟨ z, hz ⟩ : ∃ z, a = 2 * z := by
      exact even_iff_two_dvd.mp ( by simpa using ha_odd );
    exact ⟨ y, z, by rw [ sub_eq_iff_eq_add ] at hy; subst_vars; linarith ⟩
/-! ## Part 2 : the tangent-plane (rational two-square) identity -/
/-
**Lemma 2.1 (Tangent-plane identity).** Let `u, a, b` be integers with
`a² + b² = u³ - 4 =: S ≠ 0`, and let `N, R` be integers with
`R² = 4 S N² - u (u³ + 32)`.  Then `N⁶ - 4` is a sum of two rational squares.
-/
lemma tangent_identity (u a b N R : ℤ)
    (hS : a ^ 2 + b ^ 2 = u ^ 3 - 4)
    (hSne : u ^ 3 - 4 ≠ 0)
    (hR : R ^ 2 = 4 * (u ^ 3 - 4) * N ^ 2 - u * (u ^ 3 + 32)) :
    ∃ A B : ℚ, ((N : ℚ) ^ 6 - 4) = A ^ 2 + B ^ 2 := by
  use (a * (3 * u^2 * N^2 - u^3 - 8) - b * (N^2 - u) * R) / (2 * (u^3 - 4)), (b * (3 * u^2 * N^2 - u^3 - 8) + a * (N^2 - u) * R) / (2 * (u^3 - 4));
  field_simp;
  rw [ eq_div_iff ] <;> norm_cast;
  · grind +ring;
  · positivity
/-! ## Part 3 : the explicit generalized Pell family -/
/-- The constant `D = 3543121`. -/
def Dc : ℤ := 3543121
/-- The constant `C = 214359365`. -/
def Cc : ℤ := 214359365
/-- The fundamental solution component `P`. -/
def Pc : ℤ := 53319160674725436041296699414748449
/-- The fundamental solution component `Q`. -/
def Qc : ℤ := 28326330128303226243386806483560
/-- The base solution component `X₀`. -/
def X0 : ℤ := 410154078658987088294
/-- The base solution component `N₀`. -/
def N0 : ℤ := 217898400660155259
/-- The Pell sequence `(Xₖ, Nₖ)` from Lemma 3.1. -/
def pellPair : ℕ → ℤ × ℤ
  | 0 => (X0, N0)
  | (k + 1) =>
      let p := pellPair k
      (Pc * p.1 + Dc * Qc * p.2, Qc * p.1 + Pc * p.2)
/-- The `X`-component of the Pell sequence. -/
def Xpell (k : ℕ) : ℤ := (pellPair k).1
/-- The `N`-component of the Pell sequence. -/
def Npell (k : ℕ) : ℤ := (pellPair k).2
@[simp] lemma Xpell_zero : Xpell 0 = X0 := rfl
@[simp] lemma Npell_zero : Npell 0 = N0 := rfl
lemma Xpell_succ (k : ℕ) : Xpell (k + 1) = Pc * Xpell k + Dc * Qc * Npell k := rfl
lemma Npell_succ (k : ℕ) : Npell (k + 1) = Qc * Xpell k + Pc * Npell k := rfl
/-
The Pell norm identity: `Xₖ² - D Nₖ² = -C` for all `k`.
-/
lemma pell_norm (k : ℕ) : (Xpell k) ^ 2 - Dc * (Npell k) ^ 2 = -Cc := by
  induction k with
  | zero => rw [Xpell_zero, Npell_zero]; decide
  | succ k ih =>
    have hunit : Pc ^ 2 - Dc * Qc ^ 2 = 1 := by decide
    have key : (Xpell (k + 1)) ^ 2 - Dc * (Npell (k + 1)) ^ 2
        = (Pc ^ 2 - Dc * Qc ^ 2) * ((Xpell k) ^ 2 - Dc * (Npell k) ^ 2) := by
      rw [Xpell_succ, Npell_succ]; ring
    rw [key, ih, hunit]; ring
/-
Both components of the Pell sequence are positive.
-/
lemma pell_pos (k : ℕ) : 0 < Xpell k ∧ 0 < Npell k := by
  induction' k with k ih;
  · native_decide +revert;
  · exact ⟨ by rw [ Xpell_succ ] ; exact add_pos ( mul_pos ( by decide ) ih.1 ) ( mul_pos ( by decide ) ih.2 ), by rw [ Npell_succ ] ; exact add_pos ( mul_pos ( by decide ) ih.1 ) ( mul_pos ( by decide ) ih.2 ) ⟩
/-
The parity is preserved: `Xₖ` is even and `Nₖ` is odd for all `k`.
-/
lemma pell_parity (k : ℕ) : Even (Xpell k) ∧ Odd (Npell k) := by
  induction' k with k ih;
  · native_decide;
  · grind +locals
/-
The sequence `Nₖ` is strictly increasing, hence injective.
-/
lemma Npell_strictMono : StrictMono Npell := by
  refine' strictMono_nat_of_lt_succ _;
  intro k; rw [ Npell_succ ] ; nlinarith [ pell_pos k, show Qc > 0 from by decide, show Pc > 1 from by native_decide ] ;
/-! ## Part 4 : rational sums of two squares are integral sums of two squares -/
/-
**Lemma 4.2.** If a positive integer `m` is a sum of two *rational* squares, then it
is a sum of two *integer* squares.
-/
lemma rat_to_int (m : ℤ) (hm : 0 < m) (A B : ℚ) (h : (m : ℚ) = A ^ 2 + B ^ 2) :
    ∃ r s : ℤ, m = r ^ 2 + s ^ 2 := by
  -- By clearing denominators, we can rewrite the equation as $m * d^2 = p^2 + q^2$ for some integers $p, q, d$.
  obtain ⟨p, q, d, hpq, hd⟩ : ∃ p q d : ℤ, d ≠ 0 ∧ m * d^2 = p^2 + q^2 := by
    obtain ⟨p, q, d, hd_pos, h_eq⟩ : ∃ p q d : ℤ, d > 0 ∧ A = p / d ∧ B = q / d := by
      use A.num * B.den, B.num * A.den, A.den * B.den;
      simp +decide [ mul_div_mul_comm, Rat.num_div_den ];
      exact ⟨ mul_pos ( Nat.cast_pos.mpr A.pos ) ( Nat.cast_pos.mpr B.pos ), by rw [ div_mul_div_cancel₀ ( Nat.cast_ne_zero.mpr A.pos.ne' ) ] ; simp +decide [ Rat.num_div_den ] ⟩;
    obtain ⟨hA, hB⟩ := h_eq
    refine ⟨p, q, d, hd_pos.ne', ?_⟩
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hcast : (m : ℚ) * (d : ℚ) ^ 2 = (p : ℚ) ^ 2 + (q : ℚ) ^ 2 := by
      rw [h, hA, hB]; field_simp
    exact_mod_cast hcast
  have h_factor : ∀ r ∈ Nat.primeFactors (Int.natAbs (m * d^2)), r % 4 = 3 → Even (padicValNat r (Int.natAbs (m * d^2))) := by
    -- `m * d^2 = p^2 + q^2 ≥ 0`, so its `natAbs` is literally `p.natAbs^2 + q.natAbs^2`.
    have hnat : Int.natAbs (m * d^2) = Int.natAbs p ^ 2 + Int.natAbs q ^ 2 := by
      rw [hd, Int.natAbs_add_of_nonneg (sq_nonneg _) (sq_nonneg _), Int.natAbs_pow,
        Int.natAbs_pow]
    rw [hnat]
    -- A natural number that is a sum of two squares has the required factorisation property.
    exact fun r hr hr_mod =>
      Nat.eq_sq_add_sq_iff.mp ⟨Int.natAbs p, Int.natAbs q, rfl⟩ r hr hr_mod
  have h_factor_m : ∀ r ∈ Nat.primeFactors (Int.natAbs m), r % 4 = 3 → Even (padicValNat r (Int.natAbs m)) := by
    intro r hr hr'
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    haveI := Fact.mk hrp
    have hm0 : Int.natAbs m ≠ 0 := Int.natAbs_ne_zero.mpr hm.ne'
    have hd0 : Int.natAbs d ≠ 0 := Int.natAbs_ne_zero.mpr hpq
    have hrdvd : r ∣ Int.natAbs m := (Nat.mem_primeFactors.mp hr).2.1
    have hmd : Int.natAbs (m * d ^ 2) = Int.natAbs m * Int.natAbs d ^ 2 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
    have hmem : r ∈ Nat.primeFactors (Int.natAbs (m * d ^ 2)) := by
      rw [Nat.mem_primeFactors, hmd]
      exact ⟨hrp, hrdvd.mul_right _, mul_ne_zero hm0 (pow_ne_zero _ hd0)⟩
    have heven := h_factor r hmem hr'
    have hpow : padicValNat r (Int.natAbs d ^ 2)
        = 2 * padicValNat r (Int.natAbs d) := by
      rw [padicValNat.pow]; exact hd0
    rw [hmd, padicValNat.mul hm0 (pow_ne_zero _ hd0), hpow] at heven
    simpa [parity_simps] using heven
  have := @Nat.eq_sq_add_sq_iff;
  obtain ⟨ x, y, hxy ⟩ := this.mpr h_factor_m; exact ⟨ x, y, by linarith [ abs_of_pos hm ] ⟩ ;
/-! ## Part 5 : the infinitude theorem -/
/-
For every `k`, the integer `Nₖ⁶ - 4` is a sum of two integer squares.
-/
lemma Npell_sq_add_sq (k : ℕ) :
    ∃ r s : ℤ, (Npell k) ^ 6 - 4 = r ^ 2 + s ^ 2 := by
  have h_tangent : ∃ A B : ℚ, ((Npell k : ℚ)^6 - 4) = A^2 + B^2 := by
    convert tangent_identity 242 578 3720 ( Npell k ) ( 4 * Xpell k ) _ _ _ using 1 <;> norm_num;
    have := pell_norm k; norm_num [ Dc, Cc ] at this; linarith;
  have h_pos : 0 < Npell k ^ 6 - 4 := by
    exact sub_pos_of_lt ( by nlinarith [ pow_le_pow_left₀ ( by norm_num ) ( show Npell k ≥ 2 by exact le_trans ( by decide ) ( Npell_strictMono.monotone ( Nat.zero_le k ) ) ) 6 ] );
  obtain ⟨ A, B, h ⟩ := h_tangent; exact_mod_cast rat_to_int _ ( mod_cast h_pos ) _ _ ( by simpa [ ← @Rat.cast_inj ℝ ] using h ) ;
/-- For every `k`, the equation has an integer solution with `x = Nₖ`. -/
lemma exists_sol (k : ℕ) :
    ∃ p : ℤ × ℤ, p.1 ^ 2 + (Npell k) ^ 3 * p.1 + p.2 ^ 2 + 1 = 0 := by
  obtain ⟨r, s, hrs⟩ := Npell_sq_add_sq k
  obtain ⟨y, z, hyz⟩ := reduction (Npell k) r s (pell_parity k).2 hrs
  exact ⟨(y, z), hyz⟩
/-- The set of integer solutions of `y² + x³y + z² + 1 = 0`. -/
def SolSet : Set (ℤ × ℤ × ℤ) :=
  {p | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}
/-
**Theorem 5.1.** The Diophantine equation `y² + x³y + z² + 1 = 0` has infinitely many
integer solutions.
-/
theorem infinitely_many_solutions : SolSet.Infinite := by
  by_contra h_contra;
  -- By definition of $f$, we know that for each $k$, $(Npell k, (exists_sol k).choose.1, (exists_sol k).choose.2)$ is a solution.
  have h_sol : ∀ k, (Npell k, (exists_sol k).choose.1, (exists_sol k).choose.2) ∈ SolSet := by
    exact fun k => Exists.choose_spec ( exists_sol k );
  exact h_contra <| Set.infinite_of_injective_forall_mem ( fun k m hkm => by simpa using Npell_strictMono.injective <| by injection hkm ) h_sol
end Diophantine
