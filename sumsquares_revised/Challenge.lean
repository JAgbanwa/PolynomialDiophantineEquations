import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Challenge statements

Self-contained statements of the main results of the paper *On the polynomial values
represented by quadratic forms* (B. Grechuk, J. Agbanwa).  Each statement below is phrased
using only `Mathlib` notions, so that it can be read independently of the development in
`RequestProject.lean`.  Each statement is discharged in `Solution.lean`.
-/

namespace Challenge

/-- `IsSumTwoSquares n`: the positive integer `n` lies in the set `S₂` of sums of two integer
squares. -/
def IsSumTwoSquares (n : ℤ) : Prop := 0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2

/-- Property `(*)` of Section 2: for positive `a, b`, membership of two of `a`, `b`, `ab` in
`S₂` implies membership of the third. -/
def PropertyStar : Prop :=
  ∀ a b : ℤ, 0 < a → 0 < b →
    (IsSumTwoSquares a → IsSumTwoSquares b → IsSumTwoSquares (a * b)) ∧
    (IsSumTwoSquares a → IsSumTwoSquares (a * b) → IsSumTwoSquares b) ∧
    (IsSumTwoSquares b → IsSumTwoSquares (a * b) → IsSumTwoSquares a)

/-- Proposition 2.3: the equation `a x² + b x + c = v²` has infinitely many integer
solutions `x` under conditions (a), (b), (c). -/
def Proposition23 : Prop :=
  ∀ a b c x₀ v₀ : ℤ, (a = 0 ∨ (0 < a ∧ ¬ IsSquare a)) → b ^ 2 - 4 * a * c ≠ 0 →
    a * x₀ ^ 2 + b * x₀ + c = v₀ ^ 2 →
    {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite

/-- The key arithmetic statement of Section 3: `x⁶ - 4` is a sum of two squares for
infinitely many integers `x`. -/
def SumTwoSquaresSixthPower : Prop :=
  {x : ℤ | IsSumTwoSquares (x ^ 6 - 4)}.Infinite

/-- Corollary 3.1: equation (2), `y² + x³y + z² + 1 = 0`. -/
def Equation2 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite

/-- Corollary 3.2, equation (13): `y² + x³y + z² - 2 = 0`. -/
def Equation13 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite

/-- Corollary 3.2, equation (14): `y² + x³y + z² + z - 1 = 0`. -/
def Equation14 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite

/-- Corollary 3.2, equation (15): `y² + x³y + z² + z + 1 = 0`. -/
def Equation15 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite

/-- Corollary 3.2, equation (16): `y² + x³y + y + z² + 1 = 0`. -/
def Equation16 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite

/-- Proposition 4.4 (a): `2y² + yz + 2z² = x³ + 1`. -/
def Equation31a : Prop :=
  {w : ℤ × ℤ × ℤ | 2 * w.2.1 ^ 2 + w.2.1 * w.2.2 + 2 * w.2.2 ^ 2 = w.1 ^ 3 + 1}.Infinite

/-- Proposition 4.4 (b): `2y² + yz + 2z² = x³ - 1`. -/
def Equation31b : Prop :=
  {w : ℤ × ℤ × ℤ | 2 * w.2.1 ^ 2 + w.2.1 * w.2.2 + 2 * w.2.2 ^ 2 = w.1 ^ 3 - 1}.Infinite

/-- The form `2y² + yz + 2z²` is not multiplicative: it represents `2` but not `4`. -/
def FormNotMultiplicative : Prop :=
  (∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 2) ∧
    ¬ ∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 4

/-- The degenerate case `Δ = 0` of Section 4. -/
def DegenerateForms : Prop :=
  ∀ A B C : ℤ, B ^ 2 - 4 * A * C = 0 →
    ∃ k n m : ℤ, A = k * n ^ 2 ∧ B = 2 * k * n * m ∧ C = k * m ^ 2 ∧
      ∀ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = k * (n * y + m * z) ^ 2

end Challenge
