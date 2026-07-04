# Summary of changes for run 8f6e3d58-a02a-4fb2-a7d8-0f6ba8e67f2a
I formalised the paper "A Self-Contained Analysis of the Integer Equation y(x³ − z²) = z + 1" in Lean 4 (Mathlib), in `RequestProject/Main.lean`. The file builds cleanly with no `sorry`, and the main theorems check with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
Definitions and results (in namespace `Diophantine`):
- `IsSol x y z` : the predicate `y * (x^3 - z^2) = z + 1`.
- `cube_eq_one` (Lemma 2): if an integer cube equals 1 then the integer is 1.
- `fibre_neg_one` (Proposition 1): a triple `(x, y, -1)` is a solution iff `y = 0` or `x = 1`.
- `structural` (Proposition 2): a triple is a solution iff either `x³ − z² ≠ 0`, `x³ − z²` divides `z + 1` and `y = (z+1)/(x³−z²)`, or `(x, z) = (1, −1)` with `y` arbitrary.
- `structural_disjoint`: the two classes of Proposition 2 are mutually exclusive.
- `family_y_zero` (Corollary 1) and `family_x_one`: the families `(t, 0, −1)` and `(1, t, −1)` consist of solutions.
- `infinitely_many` (Theorem 1): the solution set `{p : ℤ×ℤ×ℤ | IsSol p.1 p.2.1 p.2.2}` is infinite.
Lemma 1 of the paper (zero-product property) is Mathlib's `mul_eq_zero`, so it is used directly rather than restated.
