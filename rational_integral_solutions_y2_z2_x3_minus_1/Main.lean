import Mathlib
/-!
# Rational and integral solutions of `y² + z² = x³ - 1`
This file formalizes the classification and explicit family in the accompanying paper.
The Gaussian-integer infrastructure used by the paper (Euclideanity, unique
factorization, and splitting of rational primes) is supplied by Mathlib.  The
classification is stated in terms of the equivalent sum-of-two-squares criterion,
and `integral_sum_two_squares_criterion` records its prime-valuation form.
-/
namespace CubicSumTwoSquares
/-- A natural number is represented by two integral squares. -/
def IsSumTwoIntSquares (n : ℕ) : Prop := ∃ a b : ℤ, (n : ℤ) = a ^ 2 + b ^ 2
/-- A natural number is represented by two natural squares. -/
def IsSumTwoNatSquares (n : ℕ) : Prop := ∃ a b : ℕ, n = a ^ 2 + b ^ 2
lemma intSquares_iff_natSquares (n : ℕ) :
    IsSumTwoIntSquares n ↔ IsSumTwoNatSquares n := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a.natAbs, b.natAbs, by simpa [← Int.natCast_inj] using h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by simp [h]⟩
/-
The paper's integral sum-of-two-squares theorem (Theorem 4.1).
-/
theorem integral_sum_two_squares_criterion (n : ℕ) :
    IsSumTwoIntSquares n ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  rw [intSquares_iff_natSquares]
  change (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ _
  exact Nat.eq_sq_add_sq_iff
/-
Brahmagupta–Fibonacci identity, used to combine representations.
-/
lemma sum_two_squares_mul {R : Type*} [CommRing R] (a b c d : R) :
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring
/-- The numerator pair obtained by multiplying Gaussian integers. -/
def baseU (c d e f : ℤ) : ℤ := c * e - d * f
def baseV (c d e f : ℤ) : ℤ := c * f + d * e
lemma base_norm {B M c d e f : ℤ}
    (hB : B = c ^ 2 + d ^ 2) (hM : M = e ^ 2 + f ^ 2) :
    baseU c d e f ^ 2 + baseV c d e f ^ 2 = B * M := by
  rw [ hB, hM ] ; unfold baseU baseV; ring;
/-- The projective formula (1.7). -/
def paramY (B U V u v : ℚ) : ℚ :=
  (U * (u ^ 2 - v ^ 2) - 2 * V * u * v) / (B ^ 2 * (u ^ 2 + v ^ 2))
/-- The projective formula (1.8). -/
def paramZ (B U V u v : ℚ) : ℚ :=
  (V * (u ^ 2 - v ^ 2) + 2 * U * u * v) / (B ^ 2 * (u ^ 2 + v ^ 2))
/-
Equations (1.6)–(1.8) always produce a point on the cubic surface.
-/
theorem rational_parametrization_sound
    (A B U V u v : ℚ) (hB : B ≠ 0) (huv : u ≠ 0 ∨ v ≠ 0)
    (hnorm : U ^ 2 + V ^ 2 = B * (A ^ 3 - B ^ 3)) :
    paramY B U V u v ^ 2 + paramZ B U V u v ^ 2 = (A / B) ^ 3 - 1 := by
  unfold paramY paramZ;
  field_simp;
  rw [ div_eq_iff ] <;> cases huv <;> nlinarith [ mul_self_pos.mpr ‹_› ]
/-
The paper's formulas (1.4)–(1.8), assembled directly: integral
representations of `B` and `A³-B³` produce a rational point in the fiber.
-/
theorem paper_rational_formula_sound
    (A B c d e f : ℤ) (u v : ℚ) (hB0 : B ≠ 0) (huv : u ≠ 0 ∨ v ≠ 0)
    (hB : B = c ^ 2 + d ^ 2) (hM : A ^ 3 - B ^ 3 = e ^ 2 + f ^ 2) :
    paramY B (baseU c d e f) (baseV c d e f) u v ^ 2 +
      paramZ B (baseU c d e f) (baseV c d e f) u v ^ 2 =
        ((A : ℚ) / (B : ℚ)) ^ 3 - 1 := by
  convert rational_parametrization_sound ( A : ℚ ) B ( baseU c d e f ) ( baseV c d e f ) u v ( by simpa ) huv _ using 1;
  norm_cast;
  rw [ hM, hB ] ; exact base_norm ( by ring ) ( by ring )
/- Every rational point of a nonzero circle is obtained from the projective
line by the standard quadratic formula, based at `(U,V)`. -/
theorem rational_circle_parametrization_complete
    (R U V Y Z : ℚ) (hR : R ≠ 0)
    (hbase : U ^ 2 + V ^ 2 = R) (hpoint : Y ^ 2 + Z ^ 2 = R) :
    ∃ u v : ℚ, (u ≠ 0 ∨ v ≠ 0) ∧
      Y = (U * (u ^ 2 - v ^ 2) - 2 * V * u * v) / (u ^ 2 + v ^ 2) ∧
      Z = (V * (u ^ 2 - v ^ 2) + 2 * U * u * v) / (u ^ 2 + v ^ 2) := by
  by_cases h_cases : Y = -U;
  · -- Since $V \neq 0$, we have $Z = \pm V$.
    have hZ : Z = V ∨ Z = -V := by
      grind;
    cases' hZ with hZ hZ <;> simp_all +decide;
    · grind;
    · exact ⟨ 0, 1, by norm_num ⟩;
  · refine' ⟨ U + Y, Z - V, _, _, _ ⟩; all_goals grind
/-
Completeness of the displayed formulas in every fixed admissible rational
fiber (the surjectivity assertion of Theorem 1.1).
-/
theorem rational_parametrization_complete
    (A B U V y z : ℚ) (hB : B ≠ 0) (hM : A ^ 3 - B ^ 3 ≠ 0)
    (hnorm : U ^ 2 + V ^ 2 = B * (A ^ 3 - B ^ 3))
    (hpoint : y ^ 2 + z ^ 2 = (A / B) ^ 3 - 1) :
    ∃ u v : ℚ, (u ≠ 0 ∨ v ≠ 0) ∧
      y = paramY B U V u v ∧ z = paramZ B U V u v := by
  convert rational_circle_parametrization_complete ( B * ( A ^ 3 - B ^ 3 ) ) U V ( B ^ 2 * y ) ( B ^ 2 * z ) ?_ ?_ ?_ using 1;
  · ext; simp [paramY, paramZ];
    field_simp;
    exact exists_congr fun _ => by ring_nf;
  · aesop;
  · exact hnorm;
  · grind +qlia
/-
The circle formula is injective projectively: equal points come from
proportional parameter pairs.  Together with completeness this is the
“exactly once” assertion in Theorem 1.1.
-/
theorem rational_circle_parametrization_injective
    (R U V u v u' v' : ℚ) (hR : R ≠ 0)
    (hbase : U ^ 2 + V ^ 2 = R)
    (huv : u ≠ 0 ∨ v ≠ 0) (huv' : u' ≠ 0 ∨ v' ≠ 0)
    (hy : (U * (u ^ 2 - v ^ 2) - 2 * V * u * v) / (u ^ 2 + v ^ 2) =
          (U * (u' ^ 2 - v' ^ 2) - 2 * V * u' * v') / (u' ^ 2 + v' ^ 2))
    (hz : (V * (u ^ 2 - v ^ 2) + 2 * U * u * v) / (u ^ 2 + v ^ 2) =
          (V * (u' ^ 2 - v' ^ 2) + 2 * U * u' * v') / (u' ^ 2 + v' ^ 2)) :
    u * v' = v * u' := by
  have h_nonzero : (u' ^ 2 + v' ^ 2) * (u ^ 2 + v ^ 2) ≠ 0 := by
    exact mul_ne_zero ( by cases huv' <;> positivity ) ( by cases huv <;> positivity );
  grind
/- Scaling `(u,v)` does not change the projective parametrization. -/
theorem rational_parametrization_projective
    (B U V u v t : ℚ) (ht : t ≠ 0) :
    paramY B U V (t * u) (t * v) = paramY B U V u v ∧
    paramZ B U V (t * u) (t * v) = paramZ B U V u v := by
  unfold paramY paramZ; ring_nf;
  grind
/-
The exceptional rational fiber at `x = 1`.
-/
theorem rational_fiber_one {y z : ℚ} (h : y ^ 2 + z ^ 2 = 1 ^ 3 - 1) :
    y = 0 ∧ z = 0 := by
  constructor <;> nlinarith
/-
Integral solutions have `x ≥ 1`, and the fiber at one is a singleton.
-/
theorem integral_basic_classification {x y z : ℤ}
    (h : y ^ 2 + z ^ 2 = x ^ 3 - 1) :
    1 ≤ x ∧ (x = 1 → y = 0 ∧ z = 0) := by
  exact ⟨ by nlinarith [ sq_nonneg ( x^2 ) ], fun hx => ⟨ by subst hx; nlinarith, by subst hx; nlinarith ⟩ ⟩
/-
The existence portion of Theorem 7.1, in the exact prime-valuation form.
-/
theorem integral_fiber_nonempty_iff (m : ℕ) (hm : 2 ≤ m) :
    (∃ y z : ℤ, y ^ 2 + z ^ 2 = (m : ℤ) ^ 3 - 1) ↔
      ∀ q ∈ (m ^ 3 - 1).primeFactors, q % 4 = 3 →
        Even (padicValNat q (m ^ 3 - 1)) := by
  convert integral_sum_two_squares_criterion ( m ^ 3 - 1 ) using 1;
  constructor <;> intro h;
  · obtain ⟨ y, z, h ⟩ := h; exact ⟨ y, z, by rw [ Nat.cast_sub ( by nlinarith [ pow_succ' m 2 ] ) ] ; push_cast; linarith ⟩ ;
  · obtain ⟨ a, b, h ⟩ := h; use a, b; linarith [ Nat.sub_add_cancel ( show 1 ≤ m ^ 3 from Nat.one_le_pow _ _ ( by linarith ) ) ] ;
/-
The compact construction behind Proposition 8.1.
-/
theorem polynomial_family_core (n : ℤ) (hn : Odd n) :
    let a := (n ^ 2 + 1) / 2
    let s := (n ^ 2 + 3) / 2
    let x := s ^ 2 - 1
    let y := a * x - n * s
    let z := a * s + n * x
    y ^ 2 + z ^ 2 = x ^ 3 - 1 := by
  obtain ⟨ k, rfl ⟩ := hn; ring_nf;
  norm_num [ show ( 4 + k * 4 + k ^ 2 * 4 ) = 2 * ( 2 + k * 2 + k ^ 2 * 2 ) by ring, show ( 2 + k * 4 + k ^ 2 * 4 ) = 2 * ( 1 + k * 2 + k ^ 2 * 2 ) by ring, Int.add_mul_ediv_left ] ; ring
/-
The `x`-coordinates in the explicit odd-parameter family strictly increase.
-/
theorem polynomial_family_x_strictMono :
    StrictMono (fun k : ℕ =>
      let n : ℕ := 2 * k + 1
      ((n ^ 2 + 3) / 2) ^ 2 - 1) := by
  refine' strictMono_nat_of_lt_succ fun k => _;
  rw [ tsub_lt_tsub_iff_right ] <;> ring_nf ;
  · gcongr ; omega;
  · exact Nat.one_le_pow _ _ ( Nat.div_pos ( by nlinarith ) ( by norm_num ) )
end CubicSumTwoSquares
