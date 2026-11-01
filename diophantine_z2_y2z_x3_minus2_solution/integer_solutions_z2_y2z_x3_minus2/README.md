# Integer solutions of z² + y²z + x³ − 2 = 0 — status report

**Status: OPEN.** No proof that this equation has infinitely many integer solutions has been found yet.
This folder records the computational evidence, the families shown *not* to work, and one complete
rigorous sub-result (Section 4).

## 1. Reformulation

With m = −(z + y²), a solution is the same thing as a factorisation

  z · m = x³ − 2,  z + m = −y².

In Z[α] with α = ∛2 (class number 1), this says x − α = βγ with N(β) + N(γ) = −y².
Equivalently, with w = 2z + y²: w² + 4x³ = y⁴ + 8.

## 2. Data (`data/solutions_x_le_1e7.csv`)

This is an exhaustive PARI divisor scan of all solutions with |x| ≤ 10⁷ and y ≥ 0, listing both z-roots of each (x, y).
It gives 454 rows, i.e. 227 distinct (x, y) pairs.

Cumulative (x, y) counts:

| bound on \|x\| | 10 | 10² | 10³ | 10⁴ | 10⁵ | 10⁶ | 10⁷ |
|---|---|---|---|---|---|---|---|
| (x, y) pairs | 3 | 9 | 23 | 45 | 80 | 124 | 227 |

The scan found no Pell-type (exponentially growing) sequences.

## 3. Families ruled out

- **x = q − τ² (Pell, quadratic x).** This needs q = X(2P) for P on Y² = X³ − 2.
  For P = (3,5) one gets x = (129 − T²)/100 and 27T² − 500y² = 383. That conic has no rational points
  (3-adic obstruction); the same holds for the conics from 4P and 6P.
- **Polynomial families of degree (2,1,3)** are impossible. Over ℂ they exist only with x(0) = ∛2.
- **Cubic x with cubic z (degree (1,2) split):** needs a rational root of 205379s⁶ + 61696s³ − 1024. There is none.
- **x cubic in y with y = t² + y₀**, i.e. degrees (6,2,9). By the quadratic base-change/twist argument these are
  all such families. The Singular eliminant is irreducible of degree 108 in a₃¹², so there are no rational members.
- **deg x = 6, y cubic (numerical):** the isolated real solutions are irrational. A positive-dimensional component
  is a composition of an irrational (2,1,3) family.
- **Symmetric even-k ansatz** x − α = −μ²β(t)β(−t), giving degrees (8,5,12), for δ from 2nP, n = 1..8:
  the conic∩sextic reduction has no rational members.
- **Symmetric odd-k ansatz (all odd k, including deg x = 10):** ruled out rigorously, see Section 4.

## 4. Theorem: X³ = 4v⁴ + 2 has no affine rational points

This is exactly what the odd-k symmetric ansatz would require: y(0)² = ∓2N(δ), with (q, N(δ)) on Y² = X³ − 2.

**Proof outline.** The certificate scripts are in `pari_certificate_X3_4v4_2/`; run them with `gp -q < file.gp`.

1. **Homogenise.** Write W(X³ − 2W³) = 4v⁴ with gcd(X, v, W) = 1.
   - The case W = ±A⁴ is impossible mod 4.
   - Otherwise X̂³ − 128A¹² = B⁴ with X̂ odd.
2. **Factor in Z[α].** This gives X̂ − 4A⁴α = ±ε^k β⁴ with ε = 1 + α + α².
   The cases k = 1, 2, 3 have no solutions mod 2⁴.
3. **Reduce to an elliptic curve over K.**
   - β² = c(m² + 2mnα − 2n²α²) with (m:n) ∈ P¹(Q).
   - This leads to E_K : Y² = N(q)/q, which is K-isomorphic to y² = x³ − 36x.
4. **2-descent over K** (`desc.gp`).
   - The local image dimensions are 5, 2, 1, matching theory.
   - The Selmer group has 16 elements, so rank E(K) = 2.
   - G = ⟨(−4α²+8α−8, −24α²+48), (−5α², 18)⟩ + E[2] has odd index.
5. **Saturation** (`sat.gp`, `sat2.gp`): G is ℓ-saturated for ℓ = 3, 5, 7, 11, 13, 17, 19, 29, 37, 41, 43, 109.
6. **Elliptic Chabauty at p = 5** (`chabsplit.gp`, `diag5.gp`, `sieve5.gp`).
   - The reduction groups have orders 8 and 32.
   - Only 6 cosets pass the local test, and each contains a known point.
   - All 2×2 first-order determinants are nonzero mod 5.
   - Hence m ∈ {∞, 0, 1}, which forces A = 0. ∎

## 5. Open directions

- Non-symmetric polynomial families with deg x ≥ 10 and deg y ≥ 7 (expected 2-dimensional moduli).
- The symmetric even-k ansatz for further δ values.
- Pell families with x quartic and y² = Q(τ)W(τ)².

These need exact elimination beyond what Singular managed here.

## Contents

- `data/solutions_x_le_1e7.csv`: all solutions with |x| ≤ 10⁷.
- `pari_certificate_X3_4v4_2/`: PARI/GP scripts for Section 4.
- `search_scripts/`: the exhaustive scan (`scan.gp`), quartic enumeration (`enum4.gp`),
  the cubic-x(y) Singular elimination (`q.sing`), and numerical family searches.
