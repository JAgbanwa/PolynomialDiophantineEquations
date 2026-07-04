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
# A Self-Contained Analysis of the Integer Equation `y(x³ − z²) = z + 1`
This file formalises the paper "A Self-Contained Analysis of the Integer Equation
`y(x³ − z²) = z + 1`".
The main results are:
* `Diophantine.cube_eq_one` (Lemma 2): the only integer cube equal to `1` is `x = 1`.
* `Diophantine.fibre_neg_one` (Proposition 1): exact determination of the fibre `z = -1`.
* `Diophantine.structural` (Proposition 2): the full structural characterisation of all
  integer solutions by a single divisibility condition together with the exceptional case.
* `Diophantine.infinitely_many` (Theorem 1): the equation has infinitely many integer solutions.
* `Diophantine.family_y_zero` (Corollary 1): the family `(t, 0, -1)` consists of solutions.
The zero-product property (Lemma 1 of the paper) is `mul_eq_zero` in Mathlib.
-/
namespace Diophantine
/-- The predicate that `(x, y, z)` is an integer solution of `y(x³ − z²) = z + 1`. -/
def IsSol (x y z : ℤ) : Prop := y * (x ^ 3 - z ^ 2) = z + 1
/-
**Lemma 2.** If an integer cube equals `1`, then the integer is `1`.
-/
theorem cube_eq_one {x : ℤ} (h : x ^ 3 = 1) : x = 1 := by
  nlinarith [ sq_nonneg x ]
/-
**Proposition 1.** Exact determination of the fibre `z = -1`: a triple `(x, y, -1)`
is a solution iff `y = 0` or `x = 1`.
-/
theorem fibre_neg_one (x y : ℤ) :
    IsSol x y (-1) ↔ (y = 0 ∨ x = 1) := by
  constructor <;> intro h <;> simp_all +decide [ IsSol ];
  · exact h.imp id fun h => by nlinarith [ sq_nonneg ( x^2 ) ] ;
  · aesop
/-
**Proposition 2.** A triple `(x, y, z)` is a solution iff it belongs to exactly one of the
two classes: either `x³ − z² ≠ 0` divides `z + 1` and `y = (z+1)/(x³−z²)`, or `(x, z) = (1, -1)`
with `y` arbitrary.
-/
theorem structural (x y z : ℤ) :
    IsSol x y z ↔
      (((x ^ 3 - z ^ 2 ≠ 0) ∧ (x ^ 3 - z ^ 2) ∣ (z + 1) ∧ y = (z + 1) / (x ^ 3 - z ^ 2))
        ∨ (x = 1 ∧ z = -1)) := by
  by_cases hxz : x^3 - z^2 = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : z = -1 <;> simp_all +decide [ IsSol ];
  · grind;
  · exact h1 ( by nlinarith [ sq_nonneg ( x^2 ) ] );
  · exact Ne.symm ( add_eq_zero_iff_eq_neg.not.mpr h2 );
  · exact ⟨ fun h => ⟨ ⟨ y, by linarith ⟩, by rw [ ← h, Int.mul_ediv_cancel _ hxz ] ⟩, fun h => by rw [ h.2, Int.ediv_mul_cancel h.1 ] ⟩;
  · constructor <;> intro H <;> cases' eq_or_ne ( x ^ 3 - z ^ 2 ) 0 with h h <;> simp_all +decide [ mul_comm, dvd_iff_exists_eq_mul_left ];
    · exact ⟨ ⟨ y, by linarith ⟩, by rw [ ← H, Int.mul_ediv_cancel _ h ] ⟩;
    · rw [ Int.mul_ediv_cancel' ] ; aesop
/-
The two classes in `structural` are disjoint: class (i) requires `x³ − z² ≠ 0`,
while class (ii) has `x³ − z² = 0`.
-/
theorem structural_disjoint (x y z : ℤ) :
    ¬ ((((x ^ 3 - z ^ 2 ≠ 0) ∧ (x ^ 3 - z ^ 2) ∣ (z + 1) ∧ y = (z + 1) / (x ^ 3 - z ^ 2)))
        ∧ (x = 1 ∧ z = -1)) := by
  grind
/-
**Corollary 1.** For every `t`, the triple `(t, 0, -1)` is a solution.
-/
theorem family_y_zero (t : ℤ) : IsSol t 0 (-1) := by
  unfold IsSol; norm_num;
/-
The family `(1, t, -1)` consists of solutions.
-/
theorem family_x_one (t : ℤ) : IsSol 1 t (-1) := by
  exact fibre_neg_one 1 t |>.2 ( Or.inr rfl )
/-
**Theorem 1.** The Diophantine equation `y(x³ − z²) = z + 1` has infinitely many integer
solutions.
-/
theorem infinitely_many :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Infinite := by
  exact Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun t : ℤ => ( 1, t, -1 ) ) by simp +decide [ Function.Injective ] ) fun t => family_x_one t
end Diophantine
