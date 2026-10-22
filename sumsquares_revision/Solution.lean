import RequestProject.Main

/-!
# Solution: proofs of the main results

This file is the **solution** file of the comparator setup.  It restates, word for word,
every theorem of `Challenge.lean` (namespace `Paper`) and proves it by the corresponding
theorem of the formal development `RequestProject/Main.lean` (namespace `PolyQF`).  The
definitions `PolyQF.S2`, `PolyQF.Du`, `PolyQF.bqf` and `PolyQF.AdmissibleDegrees` used in
the statements come from `RequestProject/Main.lean`, where they are defined exactly as in
`Challenge.lean`.
-/

open Polynomial PolyQF

namespace Paper

/-! ## Section 2: preliminaries and the sum of two squares case -/

/-- Equation (6): `R(t) = R(u) + R'(u)(t-u) + (t-u)² D_u(t)`. -/
theorem taylor_identity (R : ℤ[X]) (u t : ℤ) :
    R.eval t = R.eval u + R.derivative.eval u * (t - u) + (t - u) ^ 2 * (Du R u).eval t :=
  PolyQF.taylor_identity R u t

/-- Uniqueness of `D_u`: any integer polynomial satisfying the Taylor identity (6) for all
integers `t` is equal to `Du R u`. -/
theorem Du_unique (R D : ℤ[X]) (u : ℤ)
    (hD : ∀ t, R.eval t = R.eval u + R.derivative.eval u * (t - u) + (t - u) ^ 2 * D.eval t) :
    D = Du R u :=
  PolyQF.Du_unique R D u hD

/-- `deg D_u ≤ deg R - 2`. -/
theorem natDegree_Du_le (R : ℤ[X]) (u : ℤ) : (Du R u).natDegree ≤ R.natDegree - 2 :=
  PolyQF.natDegree_Du_le R u

/-- Equation (7): `4R(u)R(t) = (2R(u) + R'(u)(t-u))² + (t-u)² (4R(u)D_u(t) - R'(u)²)`. -/
theorem tangent_identity (R : ℤ[X]) (u t : ℤ) :
    4 * R.eval u * R.eval t = (2 * R.eval u + R.derivative.eval u * (t - u)) ^ 2 +
      (t - u) ^ 2 * (4 * R.eval u * (Du R u).eval t - (R.derivative.eval u) ^ 2) :=
  PolyQF.tangent_identity R u t

/-- For `R(t) = t³ + f` one has `D_u(t) = t + 2u` (Section 3). -/
theorem Du_cubic (f u : ℤ) : Du (X ^ 3 + C f) u = X + C (2 * u) :=
  PolyQF.Du_cubic f u

/-- For `R(t) = t³ + f`, the auxiliary expression `4R(u)D_u(t) - R'(u)²` equals
`4(u³+f) t - u(u³ - 8f)`; with `t = x²` this is the passage from (8) to (11). -/
theorem aux_cubic (f u t : ℤ) :
    4 * (X ^ 3 + C f : ℤ[X]).eval u * (Du (X ^ 3 + C f) u).eval t -
      ((X ^ 3 + C f : ℤ[X]).derivative.eval u) ^ 2 = 4 * (u ^ 3 + f) * t - u * (u ^ 3 - 8 * f) :=
  PolyQF.aux_cubic f u t

/-- The classical characterisation of `𝒮₂` quoted in Section 2 (from Mathlib's
`Nat.eq_sq_add_sq_iff`): a positive integer is a sum of two squares iff every prime
`p ≡ 3 (mod 4)` occurs in it with an even exponent. -/
theorem S2_iff_prime_exponents (n : ℤ) :
    n ∈ S2 ↔ 0 < n ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p n.toNat) :=
  PolyQF.S2_iff_prime_exponents n

/-- Property (*): if `a, b` are positive integers and `𝒮₂` contains two of the integers
`a, b, ab`, then it contains all three of them. -/
theorem property_star (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (a ∈ S2 → b ∈ S2 → a * b ∈ S2) ∧ (a ∈ S2 → a * b ∈ S2 → b ∈ S2) ∧
      (b ∈ S2 → a * b ∈ S2 → a ∈ S2) :=
  PolyQF.property_star a b ha hb

/-- **Proposition 2.1.** Let `R(t)` and `Q(x)` be non-constant polynomials with integer
coefficients, and let `u ∈ ℤ` satisfy `R(u) ∈ 𝒮₂`. Define `D_u` by (6). If the auxiliary
equation (8) `4R(u)D_u(Q(x)) - R'(u)² = v²` has infinitely many integer solutions
`(x, v)`, then `R(Q(x)) ∈ 𝒮₂` for infinitely many integers `x`. -/
theorem proposition_2_1 (R Q : ℤ[X]) (hR : 0 < R.natDegree) (hQ : 0 < Q.natDegree) (u : ℤ)
    (hu : R.eval u ∈ S2)
    (haux : {xv : ℤ × ℤ | 4 * R.eval u * (Du R u).eval (Q.eval xv.1) -
      (R.derivative.eval u) ^ 2 = xv.2 ^ 2}.Infinite) :
    {x : ℤ | R.eval (Q.eval x) ∈ S2}.Infinite :=
  PolyQF.proposition_2_1 R Q hR hQ u hu haux

/-- **Proposition 2.2.** Let `a, b, c ∈ ℤ`. Assume that (a) either `a = 0`, or `a > 0`
and `a` is not a perfect square, (b) `b² - 4ac ≠ 0`, and (c) equation (9)
`a x² + b x + c = v²` has an integer solution `(x₀, v₀)`. Then (9) has infinitely many
integer solutions `(x, v)`, with infinitely many distinct values of `x`.

(The paper quotes [11, Proposition 5.4] for the case `a > 0`; here that case is proved
from `PolyQF.pell_orbit_infinite` in `RequestProject/Main.lean`.) -/
theorem proposition_2_2 (a b c : ℤ) (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a))
    (hb : b ^ 2 - 4 * a * c ≠ 0) (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = v0 ^ 2) :
    {xv : ℤ × ℤ | a * xv.1 ^ 2 + b * xv.1 + c = xv.2 ^ 2}.Infinite ∧
      {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite :=
  PolyQF.proposition_2_2 a b c ha hb hc

/-- For admissible degrees, `K · D_u(Q(x)) - L` is a polynomial of degree at most two in
`x`: this is why the auxiliary equations (8) and (26) take the forms (9) and (29). -/
theorem aux_equation_quadratic (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u K L : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, K * (Du R u).eval (Q.eval x) - L = a * x ^ 2 + b * x + c :=
  PolyQF.aux_equation_quadratic R Q hdeg u K L

/-- **Algorithm 2.1, Step 2.** For admissible `(deg R, deg Q)` and any `u`, the auxiliary
equation (8) can be written in the form (9) `a x² + b x + c = v²`. -/
theorem algorithm_2_1_step2 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, 4 * R.eval u * (Du R u).eval (Q.eval x) -
      (R.derivative.eval u) ^ 2 = a * x ^ 2 + b * x + c :=
  PolyQF.algorithm_2_1_step2 R Q hdeg u

/-- **Algorithm 2.1 (correctness of the output).** Let `(deg R, deg Q)` be admissible.
If Step 1 finds `u` with `R(u) ∈ 𝒮₂`, Step 2 writes (8) as `a x² + b x + c = v²`, and
conditions (a), (b), (c) of Proposition 2.2 hold (so that the algorithm stops), then
`P(x) = R(Q(x)) ∈ 𝒮₂` for infinitely many integers `x`. -/
theorem algorithm_2_1 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u a b c : ℤ)
    (hu : R.eval u ∈ S2)
    (habc : ∀ x : ℤ, 4 * R.eval u * (Du R u).eval (Q.eval x) - (R.derivative.eval u) ^ 2 =
      a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a)) (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = v0 ^ 2) :
    {x : ℤ | R.eval (Q.eval x) ∈ S2}.Infinite :=
  PolyQF.algorithm_2_1 R Q hdeg u a b c hu habc ha hb hc

/-- **Seed test for Algorithm 2.1 in the linear case `a = 0`** (Section 2): if `b ≠ 0`,
then `b x + c = v²` has an integer solution iff `v² ≡ c (mod |b|)` for some
`0 ≤ v < |b|`; a successful residue gives `x = (v² - c)/b`. -/
theorem algorithm_2_1_linear_seed_test (b c : ℤ) (hb : b ≠ 0) :
    (∃ x v : ℤ, b * x + c = v ^ 2) ↔ ∃ v : ℤ, 0 ≤ v ∧ v < |b| ∧ b ∣ v ^ 2 - c :=
  PolyQF.algorithm_2_1_linear_seed_test b c hb

/-! ## Section 3: examples (Corollaries 3.1 and 3.2) -/

/-- Equation (2) `y² + x³y + z² + 1 = 0` is equivalent to (3)
`(x³ + 2y)² + (2z)² = x⁶ - 4`. -/
theorem equation_2_iff_3 (x y z : ℤ) :
    y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z) ^ 2 = x ^ 6 - 4 :=
  PolyQF.equation_2_iff_3 x y z

/-- The auxiliary computations of Section 3, for `R(t) = t³ + f`, `Q(x) = x²` and the
chosen `u`: equation (11) becomes `a x² + c = v²`, with the indicated values. -/
theorem aux_equations_section_3 (x : ℤ) :
    (4 * ((162 : ℤ) ^ 3 - 4) * x ^ 2 - 162 * (162 ^ 3 - 8 * (-4)) = 17006096 * x ^ 2 - 688752720) ∧
    (4 * ((2 : ℤ) ^ 3 - 4) * x ^ 2 - 2 * (2 ^ 3 - 8 * (-4)) = 16 * x ^ 2 - 80) ∧
    (4 * ((8 : ℤ) ^ 3 + 8) * x ^ 2 - 8 * (8 ^ 3 - 8 * 8) = 2080 * x ^ 2 - 3584) ∧
    (4 * ((2 : ℤ) ^ 3 + 5) * x ^ 2 - 2 * (2 ^ 3 - 8 * 5) = 52 * x ^ 2 + 64) ∧
    (4 * ((2 : ℤ) ^ 3 - 3) * x ^ 2 - 2 * (2 ^ 3 - 8 * (-3)) = 20 * x ^ 2 - 64) :=
  PolyQF.aux_equations_section_3 x

/-- The seed `u = 2` fails for `f = -4` (proof of Corollary 3.1): `u = 2` is the smallest
positive integer with `u³ - 4 ∈ 𝒮₂`, but the resulting auxiliary equation
`16x² - 80 = v²` has `a = 16`, a perfect square, so condition (a) fails. -/
theorem corollary_3_1_seed_two_fails :
    (∀ u : ℤ, 0 < u → u ^ 3 - 4 ∈ S2 → 2 ≤ u) ∧ (2 : ℤ) ^ 3 - 4 ∈ S2 ∧
      IsSquare (4 * ((2 : ℤ) ^ 3 - 4)) :=
  PolyQF.corollary_3_1_seed_two_fails

/-- Corollary 3.1, sum-of-two-squares part: `x⁶ - 4 ∈ 𝒮₂` for infinitely many integers
`x` (Algorithm 2.1 with `R(t) = t³ - 4`, `Q(x) = x²`, `u = 162`). -/
theorem corollary_3_1_sum_of_two_squares : {x : ℤ | x ^ 6 - 4 ∈ S2}.Infinite :=
  PolyQF.corollary_3_1_sum_of_two_squares

/-- **Corollary 3.1.** Equation (2) `y² + x³y + z² + 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_1 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite :=
  PolyQF.corollary_3_1

/-- Corollary 3.2, sum-of-two-squares part: for each `f ∈ {8, 5, -3}` there are infinitely
many even `x` with `x⁶ + f ∈ 𝒮₂` (seeds `u = 8, 2, 2` and `(w₀, v₀) = (6, 544), (3, 44),
(1, 4)`). -/
theorem corollary_3_2_sum_of_two_squares :
    {x : ℤ | Even x ∧ x ^ 6 + 8 ∈ S2}.Infinite ∧ {x : ℤ | Even x ∧ x ^ 6 + 5 ∈ S2}.Infinite ∧
      {x : ℤ | Even x ∧ x ^ 6 - 3 ∈ S2}.Infinite :=
  PolyQF.corollary_3_2_sum_of_two_squares

/-- Equations (13)–(15) can be rewritten in the form (17)
`(x³ + 2y)² + (2z + e)² = x⁶ + f` with `(e, f) = (0, 8), (1, 5), (1, -3)`, and equation (16)
can be rewritten as (18) `(x³ + 2y + 1)² + (2z)² = (x³ + 1)² - 4`. -/
theorem equations_13_to_16_rewritten (x y z : ℤ) :
    (y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 0) ^ 2 = x ^ 6 + 8) ∧
    (y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 1) ^ 2 = x ^ 6 + 5) ∧
    (y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 1) ^ 2 = x ^ 6 - 3) ∧
    (y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1 = 0 ↔
      (x ^ 3 + 2 * y + 1) ^ 2 + (2 * z) ^ 2 = (x ^ 3 + 1) ^ 2 - 4) :=
  PolyQF.equations_13_to_16_rewritten x y z

/-- **Corollary 3.2, equation (13).** `y² + x³y + z² - 2 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq13 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 - 2 = 0}.Infinite :=
  PolyQF.corollary_3_2_eq13

/-- **Corollary 3.2, equation (14).** `y² + x³y + z² + z - 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq14 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 - 1 = 0}.Infinite :=
  PolyQF.corollary_3_2_eq14

/-- **Corollary 3.2, equation (15).** `y² + x³y + z² + z + 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq15 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 + 1 = 0}.Infinite :=
  PolyQF.corollary_3_2_eq15

/-- **Corollary 3.2, equation (16).** `y² + x³y + y + z² + 1 = 0` has infinitely many integer
solutions (via `x = -w²` and `P(-w²) = (w⁶ - 3)(w⁶ + 1)`). -/
theorem corollary_3_2_eq16 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite :=
  PolyQF.corollary_3_2_eq16

/-- **Corollary 3.2.** Each of the equations (13)–(16) has infinitely many integer
solutions. -/
theorem corollary_3_2 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 - 2 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 - 1 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 + 1 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite :=
  PolyQF.corollary_3_2

/-- The closing remark of Section 3 on `y² + z² = x⁶ + 3`: with `R(t) = t³ + 3` and
`Q(x) = x²`, any `u` with `R(u) ∈ 𝒮₂` must be odd, and for odd `u` the auxiliary equation
(11) `4(u³+3)x² - u(u³-24) = v²` has no integer solutions (its left-hand side is
`≡ 3 (mod 4)`). Hence Algorithm 2.1 cannot resolve this equation. -/
theorem remark_x6_plus_3 :
    (∀ u : ℤ, u ^ 3 + 3 ∈ S2 → Odd u) ∧
      (∀ u : ℤ, Odd u → ∀ x v : ℤ, 4 * (u ^ 3 + 3) * x ^ 2 - u * (u ^ 3 - 24) ≠ v ^ 2) :=
  PolyQF.remark_x6_plus_3

/-! ## Section 4: general binary quadratic forms -/

/-- **Proposition 4.1, recovery formulas (28).** Assume (21), i.e.
`m = R(u) = F(p, q) ≠ 0`, let `r = R'(u)`. For every pair `(x, v)` satisfying (26)
`4 m D_u(Q(x)) - r² = -Δ v²` and the congruences (27), the integers `y, z` given by (28)
satisfy `F(y, z) = R(Q(x))`. (Exact integer division is used; the congruences guarantee that
the quotients are integers.) -/
theorem proposition_4_1_recovery (A B C : ℤ) (R Q : ℤ[X]) (u p q m r : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (x v : ℤ)
    (haux : 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = -(B ^ 2 - 4 * A * C) * v ^ 2)
    (hc1 : 2 * |m| ∣ r * p + v * (B * p + 2 * C * q))
    (hc2 : 2 * |m| ∣ r * q - v * (2 * A * p + B * q)) :
    bqf A B C (p + (Q.eval x - u) * ((r * p + v * (B * p + 2 * C * q)) / (2 * m)))
      (q + (Q.eval x - u) * ((r * q - v * (2 * A * p + B * q)) / (2 * m))) =
      R.eval (Q.eval x) :=
  PolyQF.proposition_4_1_recovery A B C R Q u p q m r hm hmF hm0 hr x v haux hc1 hc2

/-- **Proposition 4.1.** Assume (20) `Δ = B² - 4AC ≠ 0` and (21) `m = R(u) = F(p, q) ≠ 0`,
let `r = R'(u)` and let `D_u` be defined in (6). If there are infinitely many integer
pairs `(x, v)` satisfying (26) `4 m D_u(Q(x)) - r² = -Δ v²` and the congruences (27)
`rp + v(Bp + 2Cq) ≡ 0`, `rq - v(2Ap + Bq) ≡ 0 (mod 2|m|)`, then `F(y, z) = R(Q(x))` is
solvable in integers `(y, z)` for infinitely many integers `x`. -/
theorem proposition_4_1 (A B C : ℤ) (hΔ : B ^ 2 - 4 * A * C ≠ 0) (R Q : ℤ[X]) (u p q m r : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (hinf : {xv : ℤ × ℤ | 4 * m * (Du R u).eval (Q.eval xv.1) - r ^ 2 =
        -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
      2 * |m| ∣ r * p + xv.2 * (B * p + 2 * C * q) ∧
      2 * |m| ∣ r * q - xv.2 * (2 * A * p + B * q)}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, bqf A B C y z = R.eval (Q.eval x)}.Infinite :=
  PolyQF.proposition_4_1 A B C hΔ R Q u p q m r hm hmF hm0 hr hinf

/-- **Proposition 4.2.** Let `Δ = B² - 4AC`, `m ≠ 0`, and consider equation (29)
`a x² + b x + c = -Δ v²` together with the congruences (27). Assume that
(a) either `a = 0` or `-aΔ` is a positive integer that is not a perfect square,
(b) `b² - 4ac ≠ 0`, and (c) (29) has an integer solution `(x₀, v₀)` satisfying (27).
Then (29) has infinitely many integer solutions `(x, v)` satisfying (27).

(In the paper `m = R(u) = F(p, q)` and `r = R'(u)`; only `m ≠ 0` is needed here. The paper
invokes Gauss's theorem [11, Proposition 3.14] for the case `a ≠ 0`; here that case is
proved from `PolyQF.pell_orbit_infinite` in `RequestProject/Main.lean`.) -/
theorem proposition_4_2 (A B C p q r m a b c : ℤ) (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < -a * (B ^ 2 - 4 * A * C) ∧ ¬ IsSquare (-a * (B ^ 2 - 4 * A * C))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = -(B ^ 2 - 4 * A * C) * v0 ^ 2 ∧
      2 * |m| ∣ r * p + v0 * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v0 * (2 * A * p + B * q)) :
    {xv : ℤ × ℤ | a * xv.1 ^ 2 + b * xv.1 + c = -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
      2 * |m| ∣ r * p + xv.2 * (B * p + 2 * C * q) ∧
      2 * |m| ∣ r * q - xv.2 * (2 * A * p + B * q)}.Infinite :=
  PolyQF.proposition_4_2 A B C p q r m a b c hm ha hb hc

/-- **Algorithm 4.1, Step 2.** For admissible `(deg R, deg Q)`, the auxiliary equation (26)
`4 m D_u(Q(x)) - r² = -Δ v²` can be written in the form (29) `a x² + b x + c = -Δ v²`. -/
theorem algorithm_4_1_step2 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u m r : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = a * x ^ 2 + b * x + c :=
  PolyQF.algorithm_4_1_step2 R Q hdeg u m r

/-- **Algorithm 4.1 (correctness of the output).** Let `F = A y² + B y z + C z²` be
non-degenerate. If Step 1 finds `u, p, q` with `m = R(u) = F(p, q) ≠ 0`, Step 2 writes (26)
as (29) `a x² + b x + c = -Δ v²` (with `r = R'(u)`), and conditions (a)–(c) of
Proposition 4.2 hold (so that the algorithm stops), then `F(y, z) = R(Q(x))` is solvable in
integers `(y, z)` for infinitely many integers `x`.

(The degree restriction on `(R, Q)` only serves to guarantee that Step 2 is possible, see
`algorithm_4_1_step2`; it is not needed for this implication.) -/
theorem algorithm_4_1 (A B C : ℤ) (hΔ : B ^ 2 - 4 * A * C ≠ 0) (R Q : ℤ[X])
    (u p q m r a b c : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (habc : ∀ x : ℤ, 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < -a * (B ^ 2 - 4 * A * C) ∧ ¬ IsSquare (-a * (B ^ 2 - 4 * A * C))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = -(B ^ 2 - 4 * A * C) * v0 ^ 2 ∧
      2 * |m| ∣ r * p + v0 * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v0 * (2 * A * p + B * q)) :
    {x : ℤ | ∃ y z : ℤ, bqf A B C y z = R.eval (Q.eval x)}.Infinite :=
  PolyQF.algorithm_4_1 A B C hΔ R Q u p q m r a b c hm hmF hm0 hr habc ha hb hc

/-- **Seed test for Algorithm 4.1 in the linear case `a = 0`** (Section 4): if `b ≠ 0` and
`m ≠ 0`, then `b x + c = -Δ v²` has an integer solution satisfying the congruences (27) iff
some `v` with `0 ≤ v < lcm(2|m|, |b|)` satisfies (27) and `b ∣ -Δ v² - c`; then
`x = (-Δ v² - c)/b`. -/
theorem algorithm_4_1_linear_seed_test (A B C p q r m b c : ℤ) (hm : m ≠ 0) (hb : b ≠ 0) :
    (∃ x v : ℤ, b * x + c = -(B ^ 2 - 4 * A * C) * v ^ 2 ∧
      2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v * (2 * A * p + B * q)) ↔
    ∃ v : ℤ, 0 ≤ v ∧ v < (Int.lcm (2 * m) b : ℤ) ∧
      2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v * (2 * A * p + B * q) ∧
      b ∣ -(B ^ 2 - 4 * A * C) * v ^ 2 - c :=
  PolyQF.algorithm_4_1_linear_seed_test A B C p q r m b c hm hb

/-- **Proposition 4.3.** Both equations (31) `2y² + yz + 2z² = x³ + 1` and
`2y² + yz + 2z² = x³ - 1` have infinitely many integer solutions; explicitly, for every
`n ∈ ℤ` the recovery formulas give the families
`(x, y, z) = (30n² + 15n + 1, 30n³ + 45n² + 15n + 1, -120n³ - 90n² - 15n)` for (a) and
`(x, y, z) = (570n² + 225n + 24, 9690n³ + 6105n² + 1189n + 71, -4560n³ - 1230n² + 89n + 29)`
for (b). -/
theorem proposition_4_3_families (n : ℤ) :
    bqf 2 1 2 (30 * n ^ 3 + 45 * n ^ 2 + 15 * n + 1) (-120 * n ^ 3 - 90 * n ^ 2 - 15 * n) =
      (30 * n ^ 2 + 15 * n + 1) ^ 3 + 1 ∧
    bqf 2 1 2 (9690 * n ^ 3 + 6105 * n ^ 2 + 1189 * n + 71)
      (-4560 * n ^ 3 - 1230 * n ^ 2 + 89 * n + 29) = (570 * n ^ 2 + 225 * n + 24) ^ 3 - 1 :=
  PolyQF.proposition_4_3_families n

/-- **Proposition 4.3.** Both equations (31) have infinitely many integer solutions. -/
theorem proposition_4_3 :
    {s : ℤ × ℤ × ℤ | bqf 2 1 2 s.2.1 s.2.2 = s.1 ^ 3 + 1}.Infinite ∧
      {s : ℤ × ℤ × ℤ | bqf 2 1 2 s.2.1 s.2.2 = s.1 ^ 3 - 1}.Infinite :=
  PolyQF.proposition_4_3

/-- The data used in the proof of Proposition 4.3, checked against Algorithm 4.1:
for (a), `R(t) = t³ + 1`, `u = 1`, `(p, q) = (1, 0)`, `m = 2 = F(1, 0)`, `r = 3`,
`D_u(t) = t + 2`, and (26) reads `8x + 7 = 15v²`; for (b), `R(t) = t³ - 1`, `u = 7`,
`(p, q) = (3, 12)`, `m = 342 = F(3, 12)`, `r = 147`, `D_u(t) = t + 14`, and (26) reads
`456x - 819 = 5v²`. Here `Δ = 1 - 16 = -15`. -/
theorem proposition_4_3_data (x v : ℤ) :
    (bqf 2 1 2 1 0 = (X ^ 3 + C 1 : ℤ[X]).eval 1 ∧
      (X ^ 3 + C 1 : ℤ[X]).derivative.eval 1 = 3 ∧ Du (X ^ 3 + C 1) 1 = X + C 2 ∧
      (4 * 2 * (Du (X ^ 3 + C 1) 1).eval x - 3 ^ 2 = -((1 : ℤ) ^ 2 - 4 * 2 * 2) * v ^ 2 ↔
        8 * x + 7 = 15 * v ^ 2)) ∧
    (bqf 2 1 2 3 12 = (X ^ 3 + C (-1) : ℤ[X]).eval 7 ∧
      (X ^ 3 + C (-1) : ℤ[X]).derivative.eval 7 = 147 ∧
      Du (X ^ 3 + C (-1)) 7 = X + C 14 ∧
      (4 * 342 * (Du (X ^ 3 + C (-1)) 7).eval x - 147 ^ 2 =
          -((1 : ℤ) ^ 2 - 4 * 2 * 2) * v ^ 2 ↔ 456 * x - 819 = 5 * v ^ 2)) :=
  PolyQF.proposition_4_3_data x v

/-- The non-multiplicative form `F(y, z) = 2y² + yz + 2z²` of Section 4: it represents `2`
(as `F(0, 1)`), but does not represent `2 · 2 = 4`. -/
theorem non_multiplicative_example :
    bqf 2 1 2 0 1 = 2 ∧ ∀ y z : ℤ, bqf 2 1 2 y z ≠ 4 :=
  PolyQF.non_multiplicative_example

/-- The remark at the end of Section 4: the form `4(y² + z²)` is multiplicative (if it
represents positive integers `m` and `n`, it represents `mn`) and represents `4 = 4 · 1`,
but it does not represent `1`; so multiplicativity alone does not give the cancellation
direction of property (*). -/
theorem four_sum_two_squares_remark :
    (∀ m n : ℤ, (∃ y z : ℤ, m = 4 * (y ^ 2 + z ^ 2)) → (∃ y z : ℤ, n = 4 * (y ^ 2 + z ^ 2)) →
      ∃ y z : ℤ, m * n = 4 * (y ^ 2 + z ^ 2)) ∧
    (∃ y z : ℤ, (4 : ℤ) = 4 * (y ^ 2 + z ^ 2)) ∧ (∀ y z : ℤ, (1 : ℤ) ≠ 4 * (y ^ 2 + z ^ 2)) :=
  PolyQF.four_sum_two_squares_remark

/-- **Degenerate case, parametrisation.** If `B² - 4AC = 0`, then
`(A, B, C) = (k r², 2 k r s, k s²)` for some integers `k, r, s`. -/
theorem degenerate_parametrisation (A B C : ℤ) (h : B ^ 2 - 4 * A * C = 0) :
    ∃ k r s : ℤ, A = k * r ^ 2 ∧ B = 2 * k * r * s ∧ C = k * s ^ 2 :=
  PolyQF.degenerate_parametrisation A B C h

/-- In the degenerate case `F(y, z) = k (r y + s z)²`. -/
theorem degenerate_form_eq (k r s y z : ℤ) :
    bqf (k * r ^ 2) (2 * k * r * s) (k * s ^ 2) y z = k * (r * y + s * z) ^ 2 :=
  PolyQF.degenerate_form_eq k r s y z

/-- **Degenerate case, "if and only if".** Suppose `(A, B, C) = (k r², 2 k r s, k s²)`.
Then the equation `F(y, z) = P(x)` has infinitely many integer solutions `(x, y, z)` if and
only if equation (32) `k t² = P(x)` has a solution `(x₀, t₀)` with `gcd(r, s) ∣ t₀`.
(This holds for every such representation, including the trivial case
`(A, B, C) = (0, 0, 0)`.) -/
theorem degenerate_infinite_iff (A B C k r s : ℤ) (hA : A = k * r ^ 2) (hB : B = 2 * k * r * s)
    (hC : C = k * s ^ 2) (P : ℤ[X]) :
    {t : ℤ × ℤ × ℤ | bqf A B C t.2.1 t.2.2 = P.eval t.1}.Infinite ↔
      ∃ x0 t0 : ℤ, k * t0 ^ 2 = P.eval x0 ∧ (Int.gcd r s : ℤ) ∣ t0 :=
  PolyQF.degenerate_infinite_iff A B C k r s hA hB hC P

/-- Comparison with Section 2: for `F(y, z) = y² + z²` one has `Δ = -4`, and (26) becomes
`4 m D - r² = 4 v²`, i.e. (8) with `V = 2v`; conversely, every integer solution `V` of
`4 m D - r² = V²` is even (reduction modulo 4). -/
theorem comparison_with_section_2 (m r D : ℤ) :
    ((0 : ℤ) ^ 2 - 4 * 1 * 1 = -4) ∧
    (∀ v : ℤ, 4 * m * D - r ^ 2 = -((0 : ℤ) ^ 2 - 4 * 1 * 1) * v ^ 2 ↔
      4 * m * D - r ^ 2 = (2 * v) ^ 2) ∧
    (∀ V : ℤ, 4 * m * D - r ^ 2 = V ^ 2 → Even V) :=
  PolyQF.comparison_with_section_2 m r D

end Paper
