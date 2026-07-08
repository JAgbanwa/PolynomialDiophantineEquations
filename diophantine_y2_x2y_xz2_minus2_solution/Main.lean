import Mathlib
open scoped BigOperators
open scoped Classical
set_option maxHeartbeats 8000000
/-!
# Integer solutions of `y² + x²·y + x·z² − 2 = 0`
This file formalises the note *Integer Solutions of `y² + x²y + xz² − 2 = 0`*.
The main result is `Classification` (Theorem 1.1), a complete description of the integer
solution set, split according to the sign of `x`.  We also formalise the elementary
preliminaries (Section 2), the positive- and negative-`x` analyses (Sections 3–4), and the
explicit Pell-type infinite subfamily (Section 6), from which we deduce that the solution
set is infinite.
-/
namespace Diophantine
/-- The Diophantine equation `y² + x²·y + x·z² − 2 = 0`. -/
def IsSol (x y z : ℤ) : Prop := y ^ 2 + x ^ 2 * y + x * z ^ 2 - 2 = 0
/-- Family (i): the two positive-`x` exceptional solutions `(1, 1, 0)` and `(1, −2, 0)`. -/
def FamI (x y z : ℤ) : Prop :=
  (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = -2 ∧ z = 0)
/-- Family (ii): the positive-`x` middle family. -/
def FamII (x y z : ℤ) : Prop :=
  ∃ a b W : ℤ, 1 ≤ a ∧ 0 ≤ b ∧ b ≤ a ^ 2 ∧ 0 ≤ W ∧
    a * W ^ 2 = b * (a ^ 2 - b) + 2 ∧
    x = a ∧ y = -b ∧ (z = W ∨ z = -W)
/-- Family (iii): the negative-`x` family, with its two symmetric branches. -/
def FamIII (x y z : ℤ) : Prop :=
  ∃ a b W : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ 0 ≤ W ∧
    a * W ^ 2 = b * (b + a ^ 2) - 2 ∧
    x = -a ∧
      (( y = b ∧ (z = W ∨ z = -W)) ∨ (y = -a ^ 2 - b ∧ (z = W ∨ z = -W)))
/-! ## Section 2 : elementary preliminaries -/
/-
Lemma 2.1: there is no integer solution with `x = 0`.
-/
lemma no_sol_x_zero (y z : ℤ) : ¬ IsSol 0 y z := by
  exact fun h => by rw [ show IsSol 0 y z = ( y ^ 2 + 0^2 * y + 0 * z ^ 2 - 2 = 0 ) by rfl ] at h; nlinarith [ show y ≤ 1 by nlinarith, show y ≥ -1 by nlinarith ] ;
/-
Lemma 2.2: the involution `y ↦ −x² − y` preserves solutions.
-/
lemma involution (x y z : ℤ) (h : IsSol x y z) : IsSol x (-x ^ 2 - y) z := by
  unfold IsSol at *; linarith;
/-
Lemma 2.3 (discriminant form): `(x, y, z)` is a solution iff `(2y+x²)² = x⁴ − 4xz² + 8`.
-/
lemma discriminant_form (x y z : ℤ) :
    IsSol x y z ↔ (2 * y + x ^ 2) ^ 2 = x ^ 4 - 4 * x * z ^ 2 + 8 := by
  exact ⟨ fun h => by rw [ IsSol ] at h; linarith, fun h => by rw [ IsSol ] ; linarith ⟩
/-! ## Section 3 : the positive-`x` case -/
/-
Lemma 3.1: for `x = a ≥ 1`, any solution with `y ∉ [−a², 0]` is one of the two
exceptional solutions.
-/
lemma pos_outer (a y z : ℤ) (ha : 1 ≤ a) (h : IsSol a y z)
    (hy : y < -a ^ 2 ∨ 0 < y) :
    (a = 1 ∧ y = 1 ∧ z = 0) ∨ (a = 1 ∧ y = -2 ∧ z = 0) := by
  cases hy <;> simp_all +decide [ IsSol ];
  · rcases lt_trichotomy a 1 with ( H | rfl | H ) <;> rcases lt_trichotomy y ( -2 ) with ( H' | rfl | H' ) <;> try nlinarith
    exact Or.inr ⟨ rfl, rfl, by nlinarith ⟩;
  · rcases lt_trichotomy y 1 with hy | rfl | hy <;> rcases lt_trichotomy a 1 with ha | rfl | ha <;> try nlinarith
    exact Or.inl ⟨ rfl, rfl, by nlinarith ⟩
/-! ## Converse direction: every listed triple is a solution -/
/-
Each triple in family (i) is a solution.
-/
lemma famI_isSol (x y z : ℤ) (h : FamI x y z) : IsSol x y z := by
  rcases h with ( ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ ) <;> trivial
/-
Each triple in family (ii) is a solution.
-/
lemma famII_isSol (x y z : ℤ) (h : FamII x y z) : IsSol x y z := by
  obtain ⟨ a, b, W, ha, hb, hb', hW, h₁, rfl, rfl, rfl | rfl ⟩ := h <;> ring_nf at * <;> simp_all +decide [ IsSol ];
  · ring;
  · grind
/-
Each triple in family (iii) is a solution.
-/
lemma famIII_isSol (x y z : ℤ) (h : FamIII x y z) : IsSol x y z := by
  grind +locals
/-! ## Section 5 : the complete classification (Theorem 1.1) -/
/-
**Theorem 1.1.** The integer solutions of `y² + x²·y + x·z² − 2 = 0` are exactly the
members of the three families (i), (ii), (iii).
-/
theorem Classification (x y z : ℤ) :
    IsSol x y z ↔ FamI x y z ∨ FamII x y z ∨ FamIII x y z := by
  constructor;
  · by_cases hx : x = 0;
    · exact fun h => False.elim <| no_sol_x_zero y z <| by simpa [ hx ] using h;
    · cases lt_or_gt_of_ne hx <;> intro h <;> simp_all +decide [ IsSol ];
      · -- From h, y*(y+x^2) = 2 + a*z^2 ≥ 2 > 0 (since a ≥ 1, z^2 ≥ 0), hence y > 0 or y < -x^2
        by_cases hy : y > 0 ∨ y < -x^2;
        · cases hy;
          · exact Or.inr <| Or.inr <| ⟨ -x, y, |z|, by linarith, by linarith, by positivity, by nlinarith [ abs_mul_abs_self z ], by linarith, Or.inl ⟨ by linarith, by cases abs_cases z <;> omega ⟩ ⟩;
          · refine Or.inr <| Or.inr <| ⟨ -x, -x ^ 2 - y, |z|, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> try nlinarith;
            · positivity;
            · rw [ sq_abs ] ; linarith;
            · exact Or.inr ⟨ by ring, eq_or_eq_neg_of_abs_eq rfl ⟩;
        · push Not at hy;
          nlinarith [ sq_nonneg ( x + z ), mul_self_pos.2 hx ];
      · by_cases hy : y < -x^2 ∨ 0 < y;
        · rcases pos_outer x y z ( by linarith ) h hy with ( ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ ) <;> [ exact Or.inl ( Or.inl ⟨ rfl, rfl, rfl ⟩ ) ; exact Or.inl ( Or.inr ⟨ rfl, rfl, rfl ⟩ ) ];
        · refine Or.inr <| Or.inl ⟨ x, -y, |z|, by linarith, by push Not at hy; linarith, by push Not at hy; nlinarith, by positivity, ?_, rfl, ?_, ?_ ⟩ <;> simp_all +decide;
          · linarith;
          · exact eq_or_eq_neg_of_abs_eq rfl;
  · rintro ( h | h | h ) <;> [ exact famI_isSol _ _ _ h; exact famII_isSol _ _ _ h; exact famIII_isSol _ _ _ h ]
/-! ## Section 6 : an explicit Pell-type infinite subfamily -/
/-- The pair sequence `(Uₙ, Zₙ)` from Proposition 6.1. -/
def pell : ℕ → ℤ × ℤ
  | 0 => (573, 60)
  | (n + 1) =>
      let p := pell n
      (33 * p.1 + 272 * p.2, 4 * p.1 + 33 * p.2)
/-- The `U`-sequence. -/
def pellU (n : ℕ) : ℤ := (pell n).1
/-- The `Z`-sequence. -/
def pellZ (n : ℕ) : ℤ := (pell n).2
/-
Basic invariants of the Pell sequence: positivity, oddness of `Uₙ`, and the Pell
relation `Uₙ² − 68·Zₙ² = 83529`.
-/
lemma pell_props (n : ℕ) :
    0 < pellU n ∧ 0 < pellZ n ∧ Odd (pellU n) ∧
      pellU n ^ 2 - 68 * pellZ n ^ 2 = 83529 := by
  induction' n with n ih <;> norm_num [ pellU, pellZ, pell ] at *;
  grind +qlia
/-
`Uₙ` is strictly increasing.
-/
lemma pellU_strictMono : StrictMono pellU := by
  exact strictMono_nat_of_lt_succ fun n => by have := pell_props n; have := pell_props ( n + 1 ) ; norm_num [ pellU, pellZ, pell ] at * ; linarith;
/-
Proposition 6.1: the Pell sequence yields integer solutions with `x = −17`.
Both branches `y = (Uₙ − 289)/2` and `y = (−Uₙ − 289)/2` are captured via `2y + 289 = ±Uₙ`.
-/
lemma pell_gives_sol (n : ℕ) :
    (∃ y : ℤ, 2 * y + 289 = pellU n ∧ IsSol (-17) y (pellZ n)) ∧
    (∃ y : ℤ, 2 * y + 289 = -pellU n ∧ IsSol (-17) y (pellZ n)) := by
  obtain ⟨ k, hk ⟩ := pell_props n |>.2.2.1;
  constructor;
  · use k - 144;
    exact ⟨ by linarith, by rw [ IsSol ] ; nlinarith [ pell_props n |>.2.2.2 ] ⟩;
  · refine' ⟨ -k - 145, _, _ ⟩ <;> norm_num [ hk, IsSol ];
    · grind;
    · have := pell_props n |>.2.2.2; rw [ hk ] at this; linarith;
/-
The full integer solution set is infinite.
-/
theorem sol_infinite :
    Set.Infinite {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2} := by
  -- By contradiction, assume the set is finite.
  by_contra h_finite;
  -- By definition of $f$, we know that for each $n$, $( -17, y_n, z_n )$ is a solution.
  have h_finite_solutions : Set.Finite {p : ℤ × ℤ × ℤ | ∃ n : ℕ, p = (-17, Classical.choose (pell_gives_sol n).1, pellZ n)} := by
    exact Set.Finite.subset ( Set.not_infinite.mp h_finite ) fun p hp => by obtain ⟨ n, rfl ⟩ := hp; exact Classical.choose_spec ( pell_gives_sol n |>.1 ) |>.2;
  refine h_finite_solutions.not_infinite <| Set.infinite_of_injective_forall_mem ( fun n m hnm => ?_ ) fun n => ⟨ n, rfl ⟩;
  have := Classical.choose_spec ( pell_gives_sol n |>.1 );
  have := Classical.choose_spec ( pell_gives_sol m |>.1 );
  exact pellU_strictMono.injective ( by linarith [ show pellU n = pellU m from by aesop ] )
end Diophantine
