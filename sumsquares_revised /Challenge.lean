import Mathlib

/-!
# Challenge: the main results of *On the polynomial values represented by quadratic forms*

This file is the small, human-auditable statement surface for the formalization of

  *On the polynomial values represented by quadratic forms*,
  by Bogdan Grechuk and Jamal Agbanwa.

It imports only Mathlib, defines nothing new, and states the paper's main results in
elementary terms: every claim below says that a set of integers, or of integer triples,
is infinite (`Set.Infinite`).  Solution.lean, which may import the whole proof
development, contains the identical declarations together with their proofs.

The statements are, in order:

* `sum_two_squares_x_pow_six_sub_four` — the abstract's sum-of-two-squares claim:
  `x⁶ − 4` is a sum of two squares for infinitely many integers `x`;
* `equation_2_infinite` — Proposition 3.1, the paper's headline result: the equation
  `y² + x³y + z² + 1 = 0` (equation (2)), previously the shortest equation for which
  finiteness of the integer solution set was open, has infinitely many integer solutions;
* `equation_14_infinite`, `equation_15_infinite`, `equation_16_infinite`,
  `equation_17_infinite` — Proposition 3.2, the four length-9 equations (14)–(17);
* `prop_4_1_general_form` — Proposition 4.1, the tangent construction for an arbitrary
  non-degenerate binary quadratic form `F(y,z) = A y² + B y z + C z²`;
* `prop_4_2_auxiliary_equation` — Proposition 4.2, infinitude of the solutions of the
  auxiliary equation (30) inside a prescribed congruence class;
* `form_2_1_2_eq_cube_add_one_infinite`, `form_2_1_2_eq_cube_sub_one_infinite` —
  Proposition 4.4, for the non-multiplicative form `2y² + yz + 2z²`.

Throughout, a triple `p : ℤ × ℤ × ℤ` is read as `(x, y, z) = (p.1, p.2.1, p.2.2)`.

The `sorry` in each proof below is deliberate: this module advertises the statements
only, and Solution.lean supplies the proofs.
-/

namespace PolynomialValuesQuadraticForms

/-! ## Section 2–3: the sum of two squares -/

/-- **Abstract, and Section 3.**  `x⁶ − 4` is a sum of two squares for infinitely many
integers `x`.  (Equivalently, the equation `Y² + Z² = x⁶ − 4`, i.e. equation (3), has
infinitely many integer solutions.) -/
theorem sum_two_squares_x_pow_six_sub_four :
    {x : ℤ | ∃ a b : ℤ, x ^ 6 - 4 = a ^ 2 + b ^ 2}.Infinite := by
  sorry

/-- **Proposition 3.1.**  The Diophantine equation `y² + x³y + z² + 1 = 0`, equation (2)
of the paper, has infinitely many integer solutions `(x, y, z)`. -/
theorem equation_2_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  sorry

/-- **Proposition 3.2, equation (14).**  `y² + x³y + z² − 2 = 0` has infinitely many
integer solutions. -/
theorem equation_14_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite := by
  sorry

/-- **Proposition 3.2, equation (15).**  `y² + x³y + z² + z − 1 = 0` has infinitely many
integer solutions. -/
theorem equation_15_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite := by
  sorry

/-- **Proposition 3.2, equation (16).**  `y² + x³y + z² + z + 1 = 0` has infinitely many
integer solutions. -/
theorem equation_16_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite := by
  sorry

/-- **Proposition 3.2, equation (17).**  `y² + x³y + y + z² + 1 = 0` has infinitely many
integer solutions. -/
theorem equation_17_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  sorry

/-! ## Section 4: general binary quadratic forms -/

/-- **Proposition 4.1.**  The tangent construction for a general binary quadratic form.

Let `F(y,z) = A y² + B y z + C z²` be non-degenerate, i.e. `Δ = B² − 4AC ≠ 0`, let
`R` and `Q` be integer polynomial functions, let `u` be an integer with
`R u = F(p, q) ≠ 0`, let `r = R'(u)` and let `Du` be the second-order Taylor coefficient
of `R` at `u`, so that `R t = R u + r (t − u) + (t − u)² Du t` for all `t`.

If the auxiliary equation (27),

  `4 R(u) Du(Q(x)) − r² = −Δ v²`,

together with the congruence conditions (28),

  `2|R(u)| ∣ r p + v (B p + 2 C q)` and `2|R(u)| ∣ r q − v (2 A p + B q)`,

has infinitely many integer solutions `(x, v)`, then `F(y, z) = R(Q(x))` is solvable in
integers `y, z` for infinitely many integers `x`. -/
theorem prop_4_1_general_form {A B C : ℤ} (u p q r : ℤ) (R Q Du : ℤ → ℤ)
    (hΔ : B ^ 2 - 4 * A * C ≠ 0)
    (hm : R u = A * p ^ 2 + B * p * q + C * q ^ 2) (hmne : R u ≠ 0)
    (hTaylor : ∀ t, R t = R u + r * (t - u) + (t - u) ^ 2 * Du t)
    (hInf : {xv : ℤ × ℤ |
        4 * R u * Du (Q xv.1) - r ^ 2 = -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
        (2 * |R u|) ∣ (r * p + xv.2 * (B * p + 2 * C * q)) ∧
        (2 * |R u|) ∣ (r * q - xv.2 * (2 * A * p + B * q))}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = R (Q x)}.Infinite := by
  sorry

/-- **Proposition 4.2.**  The auxiliary equation (30), `a x² + b x + c = −D v²`, together
with a congruence condition `cg` on `v` which is periodic with period `2m` (`m ≠ 0`).
Under the paper's conditions (a) `a = 0` or `a(−D)` is a positive non-square,
(b) `b² − 4ac ≠ 0`, and (c) there is one solution `(x₀, v₀)` with `cg v₀`, the equation
has infinitely many integer solutions `(x, v)` with `cg v`. -/
theorem prop_4_2_auxiliary_equation {a b c D m : ℤ} (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < a * (-D) ∧ ¬ IsSquare (a * (-D))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (cg : ℤ → Prop) (hperiod : ∀ v w : ℤ, cg v → cg (v + 2 * m * w))
    (x0 v0 : ℤ) (hsol : a * x0 ^ 2 + b * x0 + c = -D * v0 ^ 2) (hc0 : cg v0) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + b * p.1 + c = -D * p.2 ^ 2 ∧ cg p.2}.Infinite := by
  sorry

/-- **Proposition 4.4(a).**  The equation `2y² + yz + 2z² = x³ + 1`, for the
non-multiplicative form `2y² + yz + 2z²`, has infinitely many integer solutions. -/
theorem form_2_1_2_eq_cube_add_one_infinite :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 + 1}.Infinite := by
  sorry

/-- **Proposition 4.4(b).**  The equation `2y² + yz + 2z² = x³ − 1` has infinitely many
integer solutions. -/
theorem form_2_1_2_eq_cube_sub_one_infinite :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 - 1}.Infinite := by
  sorry

end PolynomialValuesQuadraticForms
