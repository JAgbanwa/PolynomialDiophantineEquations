import RequestProject.Represent
/-!
# Proposition 4.4: a non-multiplicative form
The binary quadratic form `F(y,z) = 2y² + yz + 2z²` is the simplest form that is not
multiplicative.  Algorithm 4.3 nonetheless resolves both equations of (32):
* (32a) `2y² + yz + 2z² = x³ + 1`, with the explicit family
  `x = 30n²+15n+1`, `y = 30n³+45n²+15n+1`, `z = −(120n³+90n²+15n)`;
* (32b) `2y² + yz + 2z² = x³ − 1`, with the explicit family
  `x = 570n²+225n+24`, `y = 3+(570n²+225n+17)(4+17n)`,
  `z = 12+(570n²+225n+17)(1−8n)`.
Both families are verified directly, so this section is fully self-contained.
-/
namespace SumSquares
open scoped BigOperators
/-
**Proposition 4.4(a).** `2y² + yz + 2z² = x³ + 1` has infinitely many solutions.
-/
theorem prop_4_4_a :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 + 1}.Infinite := by
  apply infinite_of_inj
    (P := fun x y z => 2 * y ^ 2 + y * z + 2 * z ^ 2 = x ^ 3 + 1)
    (g := fun n : ℕ =>
      ((30 * (n : ℤ) ^ 2 + 15 * (n : ℤ) + 1,
        30 * (n : ℤ) ^ 3 + 45 * (n : ℤ) ^ 2 + 15 * (n : ℤ) + 1,
        -(120 * (n : ℤ) ^ 3 + 90 * (n : ℤ) ^ 2 + 15 * (n : ℤ))) : ℤ × ℤ × ℤ))
  ·
    exact fun a b h => by norm_num at h; exact_mod_cast ( by nlinarith : ( a : ℤ ) = b )
  · intro n; push_cast; ring
/-
**Proposition 4.4(b).** `2y² + yz + 2z² = x³ − 1` has infinitely many solutions.
-/
theorem prop_4_4_b :
    {p : ℤ × ℤ × ℤ | 2 * p.2.1 ^ 2 + p.2.1 * p.2.2 + 2 * p.2.2 ^ 2 = p.1 ^ 3 - 1}.Infinite := by
  apply infinite_of_inj
    (P := fun x y z => 2 * y ^ 2 + y * z + 2 * z ^ 2 = x ^ 3 - 1)
    (g := fun n : ℕ =>
      ((570 * (n : ℤ) ^ 2 + 225 * (n : ℤ) + 24,
        3 + (570 * (n : ℤ) ^ 2 + 225 * (n : ℤ) + 17) * (4 + 17 * (n : ℤ)),
        12 + (570 * (n : ℤ) ^ 2 + 225 * (n : ℤ) + 17) * (1 - 8 * (n : ℤ))) : ℤ × ℤ × ℤ))
  ·
    exact fun a b h => by norm_num at h; nlinarith
  · intro n; push_cast; ring
end SumSquares
