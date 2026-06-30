import Mathlib
open scoped BigOperators
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# An explicit infinite family of integer solutions to `y² + x³y + z² - 2 = 0`
This file formalises the paper *An Explicit Infinite Family of Integer Solutions to
`y² + x³y + z² − 2 = 0`*.
The equation under study is
`y² + x³ y + z² − 2 = 0`  (1.1)
and the main result (Theorem 1.1) is that it has infinitely many integer solutions.
The construction uses the Pell-type sequence
`(c₀, d₀) = (1, 0)`, `cₙ₊₁ = 3cₙ + 4dₙ`, `dₙ₊₁ = 2cₙ + 3dₙ`  (1.2)
and explicit formulas (1.3) for the solution triples.
-/
namespace DiophantineY2X3Y
/-- The Pell pair sequence `(cₙ, dₙ)` defined by `(c₀, d₀) = (1, 0)`,
`cₙ₊₁ = 3cₙ + 4dₙ`, `dₙ₊₁ = 2cₙ + 3dₙ`. -/
def cd : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | (n + 1) => (3 * (cd n).1 + 4 * (cd n).2, 2 * (cd n).1 + 3 * (cd n).2)
/-- The `c` component of the Pell sequence. -/
def c (n : ℕ) : ℤ := (cd n).1
/-- The `d` component of the Pell sequence. -/
def d (n : ℕ) : ℤ := (cd n).2
@[simp] lemma c_zero : c 0 = 1 := rfl
@[simp] lemma d_zero : d 0 = 0 := rfl
lemma c_succ (n : ℕ) : c (n + 1) = 3 * c n + 4 * d n := rfl
lemma d_succ (n : ℕ) : d (n + 1) = 2 * c n + 3 * d n := rfl
/-- Auxiliary quantity `aₙ = 2cₙ² − 1`. -/
def a (n : ℕ) : ℤ := 2 * (c n) ^ 2 - 1
/-- Auxiliary quantity `Rₙ = 2cₙ(aₙ − 1)`. -/
def R (n : ℕ) : ℤ := 2 * c n * (a n - 1)
/-- Auxiliary quantity `Sₙ = aₙ² − aₙ − 1`. -/
def S (n : ℕ) : ℤ := (a n) ^ 2 - a n - 1
/-- The `x` component of the constructed solution: `xₙ = 4cₙdₙ`. -/
def xx (n : ℕ) : ℤ := 4 * c n * d n
/-- The `z` component of the constructed solution: `zₙ = aₙ(Rₙ − Sₙ)`. -/
def zz (n : ℕ) : ℤ := a n * (R n - S n)
/-- The `y` component of the constructed solution.
In the paper `yₙ = aₙ(Rₙ + Sₙ) − xₙ³/2`; since `xₙ = 4cₙdₙ` we have
`xₙ³/2 = 32 cₙ³ dₙ³`, which we use to avoid integer division. -/
def yy (n : ℕ) : ℤ := a n * (R n + S n) - 32 * (c n) ^ 3 * (d n) ^ 3
/-- Lemma 3.1 (Pell identity): `cₙ² − 2dₙ² = 1` for all `n`. -/
lemma pell (n : ℕ) : (c n) ^ 2 - 2 * (d n) ^ 2 = 1 := by
  induction' n with n ih <;> norm_num [ *, c_succ, d_succ ];
  grind
/-- `cₙ > 0` for all `n`. -/
lemma c_pos (n : ℕ) : 0 < c n := by
  induction' n with n ih;
  · decide +revert;
  · -- By definition of $c$, we have $c (n + 1) = 3 * c n + 4 * d n$.
    have h_c_succ : c (n + 1) = 3 * c n + 4 * d n := by
      rfl;
    nlinarith [ pell n ]
/-- `dₙ ≥ 0` for all `n`. -/
lemma d_nonneg (n : ℕ) : 0 ≤ d n := by
  induction' n with n ih <;> norm_num [ * ];
  exact add_nonneg ( mul_nonneg zero_le_two ( c_pos n |> le_of_lt ) ) ( mul_nonneg zero_le_three ih )
/-- `dₙ > 0` for all `n ≥ 1`. -/
lemma d_pos (n : ℕ) : 0 < d (n + 1) := by
  exact Nat.recOn n ( by decide ) fun n ih => by rw [ d_succ ] ; linarith [ c_pos n, c_succ n, d_succ n ] ;
/-- `cₙ` is strictly increasing: `cₙ < cₙ₊₁`. -/
lemma c_lt (n : ℕ) : c n < c (n + 1) := by
  exact by have := c_succ n; have := d_succ n; have := c_pos n; have := d_nonneg n; linarith;
/-- `dₙ` is strictly increasing: `dₙ < dₙ₊₁`. -/
lemma d_lt (n : ℕ) : d n < d (n + 1) := by
  norm_num [ d_succ ];
  linarith [ c_pos n, d_nonneg n ]
/-- The main algebraic identity (Theorem 1.1 / Lemma 5.1): for every `n`,
the triple `(xₙ, yₙ, zₙ)` solves the equation `y² + x³y + z² − 2 = 0`. -/
lemma solution (n : ℕ) :
    (yy n) ^ 2 + (xx n) ^ 3 * (yy n) + (zz n) ^ 2 - 2 = 0 := by
      unfold yy xx zz a R S;
      unfold a;
      grind +suggestions
/-- The sequence `n ↦ xₙ₊₁` is strictly monotone (so the produced solutions are distinct). -/
lemma xx_strictMono : StrictMono (fun n : ℕ => xx (n + 1)) := by
  refine' strictMono_nat_of_lt_succ _;
  intro n;
  unfold xx;
  gcongr <;> nlinarith [ c_pos n, c_pos ( n + 1 ), d_pos n, d_pos ( n + 1 ), c_lt n, c_lt ( n + 1 ), d_lt n, d_lt ( n + 1 ) ]
/-- The set of integer solutions to `y² + x³y + z² − 2 = 0`. -/
def solutionSet : Set (ℤ × ℤ × ℤ) :=
  {p | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}
/-- **Theorem 1.1.** The equation `y² + x³y + z² − 2 = 0` has infinitely many
integer solutions. -/
theorem infinite_solutions : solutionSet.Infinite := by
  -- Define the function `f: ℕ → ℤ × ℤ × ℤ` by `f n = (xx (n+1), yy (n+1), zz (n+1))`.
  set f : ℕ → ℤ × ℤ × ℤ := fun n => (xx (n + 1), yy (n + 1), zz (n + 1));
  -- Show that `f` is injective.
  have h_inj : Function.Injective f := by
    intros m n hmn
    simp [f] at hmn
    exact xx_strictMono.injective hmn.left;
  exact Set.infinite_of_injective_forall_mem h_inj fun n => solution _
end DiophantineY2X3Y
