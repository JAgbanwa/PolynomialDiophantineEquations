# Open problems from `open.pdf` — status of this project
The attached paper (B. Grechuk, *A systematic approach to Diophantine equations:
open problems*) collects the smallest Diophantine equations that are currently open
for six different questions (Problems 1–6).  This file records, honestly, what was
attempted here and what was actually proved.
## What is proved (machine-checked, no `sorry`)
`RequestProject/Table5Pell.lean` concerns the equation
```
y² + x²y + z²x − 2 = 0                                     (H = 22, Table 5)
```
for which **Problem 2** ("does it have, for every k, a solution with
min(|x|,|y|,|z|) ≥ k?") is listed as open.
* `Table5.pell_iff` — for a fixed `x = −m`, the equation is solvable iff the
  Pell-type equation `w² − 4mz² = m⁴ + 8` is solvable (`w = 2y + m²`).
* `Table5.table5_step` — an explicit solution-generating map: from a solution of
  `s² + s = mU²` (i.e. `T² − 4mU² = 1` with `T = 2s+1`) and a solution `(y, z)`,
  the pair `((2s+1)y + 2mUz + m²s, 2Uy + (2s+1)z + m²U)` is again a solution.
* `Table5.large_of_base` — if `m ≥ 1`, `4m` is not a perfect square, and there is
  *one* solution with `x = −m`, then there are solutions with `x = −m` and with
  `y`, `z` arbitrarily large.  In particular the equation has infinitely many
  integer solutions (e.g. all with `x = −17`).
* `Table5.problem2_of_base`, `Table5.problem2_le_4591` — consequently, for every
  `k ≤ 4591` the equation has a solution with `min(|x|,|y|,|z|) ≥ k`.
* `Table5.problem2_of_unbounded_good` — Problem 2 for this equation would follow
  from the existence of arbitrarily large `m` (with `4m` a non-square) admitting one
  solution with `x = −m`.
**Problem 2 for this equation is therefore *not* resolved**: what is missing is a
proof that the set of such `m` is unbounded.  Computer search (see `search/`) found
`m = 17, 31, 71, 79, 97, 142, 193, 199, 241, 433, 487, 553, 622, 823, 1241, 1246,
1297, 1351, 1423, 1609, 1801, 4591, …`, and the largest of these is what gives the
bound `4591` above.
## What was attempted and did not work
* **Table 5, `y² + x²y + z²x − 2 = 0`.**  Searches for a polynomial family
  `(m(t), y(t), z(t))` (equivalently for a section of the elliptic surface
  `U² = Y³ − 2d²Y + d⁵` over `ℚ(d)`, which parametrises the reduced problem
  `d z² = d² + y³ − 2y`) produced only irrational solutions; an exhaustive search over
  integer coefficient polynomials of degree ≤ 2 with coefficients bounded by 6–8
  found none.  Vieta-type involutions on the cubic surface do not increase `|x|`.
* **Table 5, `z² + y²z + x³ − 2 = 0`** (also Table 7, Problem 4).  The equation is
  `z(z + y²) = 2 − x³`, so for each `x` there are only finitely many solutions; a
  heuristic count suggests only finitely many solutions overall, which would make the
  answer to Problem 2 negative but is out of reach.  A search for polynomial families
  with `y` linear in the parameter produced only irrational solutions.
* **Table 11, `y(x³ − z²) = x`** (Problem 2; also equation (12), `H = 26`).  Every
  solution with `x ≠ 0` satisfies `x = εa²y`, `z = ±ab`, `y³a⁴ − 1 = εb²`
  (`ε = ±1`), i.e. it comes from `b² = n³a⁴ ∓ 1`; large `min(|x|,|y|,|z|)` requires
  `n = |y|` large.  A search over `a ≤ 30`, `n ≤ 20000` found only the known
  solutions `(x,y,z) = (2,−2,±3)` and degenerate ones.  (This reduction is the known
  one to `x⁴y³ = z² ± 1` mentioned in the paper.)
* **Table 6 (Problem 3, plane quartics), Tables 9–10 (Problem 6)** — extensive
  searches in earlier sessions found no solutions; the C programs are in `search/`.
## Conclusion
No open problem of the paper was fully resolved.  The Lean file contains only
statements that are completely proved, and the partial nature of the Problem 2 result
is stated explicitly in `Table5.problem2_of_unbounded_good` and in the file header.
---
## Session 3: Table 6 (Problem 3), two quartic equations
Problem 3 asks whether a given *homogeneous* equation has an integer solution in
which **all** variables are nonzero.  Two of the five equations of Table 6 were
attacked here, with the following complete (machine-checked, `sorry`-free)
partial results.
### The equation `x⁴ + y⁴ + z³t − zt³ = 0`  (`RequestProject/Table6Quartic.lean`)
Rewriting it as `x⁴ + y⁴ = z t (t − z)(t + z)`, a sum of two fourth powers is the
area of a Pythagorean triangle.
* `Table6.no_solution_of_isCoprime` — no solution with `gcd(x, y) = 1`.
* `Table6.no_solution_of_isCoprime_zt_of_not_both_even` — no solution with
  `gcd(z, t) = 1` in which `x` and `y` are not both even.
### The equation `x⁴ + x y³ + z⁴ + t⁴ = 0`  (`Table6Quartic2.lean`, `Table6Quartic3.lean`)
Here `z⁴ + t⁴ = A B C` with `A = −x`, `B = x + y`, `C = x² − xy + y² = B² + 3AB + 3A²`.
* `Table6.no_solution_of_isCoprime_zt` — no solution with `gcd(z, t) = 1`.
* `Table6.no_solution_of_isCoprime_xy` — no solution with `gcd(x, y) = 1` and
  `16 ∤ x(x + y)`;
* `Table6.no_solution_of_isCoprime_xy_of_not_both_even` — the same statement in
  its natural form: no solution with `gcd(x, y) = 1` in which `z` and `t` are not
  both even.
### Supporting theory
* `RequestProject/SumFourthPowers.lean` — the classical facts about a *primitive*
  sum of two fourth powers `N = x⁴ + y⁴`, `gcd(x, y) = 1`: every odd prime divisor
  is `≡ 1 (mod 8)`, every odd divisor is `≡ ±1 (mod 8)`, and `N ≡ 1, 2 (mod 16)`.
* `RequestProject/FourthPowerValuation.lean` — the same theory **without** a
  coprimality assumption.  The key point is that an odd prime `p ≢ 1 (mod 8)`
  dividing `z⁴ + t⁴` must divide both `z` and `t`, so that the exponent of such a
  `p` in `z⁴ + t⁴` is always a multiple of `4`.  Consequences:
  `SumFourthPowers.four_dvd_or_sixteen_dvd` (`4 ∣ z⁴ + t⁴ → 16 ∣ z⁴ + t⁴`) and
  `SumFourthPowers.exact_divisor_mod_eight`: if `z⁴ + t⁴ = F · G` with `F` odd and
  `gcd(F, G) = 1`, then `|F| ≡ 1 (mod 8)`.
### What is still missing
Both equations are homogeneous, so a hypothetical all-nonzero solution can only
be normalised by `gcd(x, y, z, t) = 1`.  The cases that survive are:
* `x⁴ + y⁴ + z³t − zt³ = 0`: `gcd(x, y) > 1`, and either `gcd(z, t) > 1` or `x`
  and `y` both even;
* `x⁴ + x y³ + z⁴ + t⁴ = 0`: `gcd(z, t) > 1`, and either `gcd(x, y) > 1` or `z`
  and `t` both even (equivalently `16 ∣ x(x + y)`).
In these cases the `2`- and `3`-adic information used above is genuinely
insufficient: the mod-8 case analysis leaves two families of candidate
factorisations (`16 ∣ x` resp. `16 ∣ x + y` for the second equation), and
computer search confirms that arithmetically consistent candidates of that shape
do exist (although no actual solution was found).
### Searches performed
* `search/e4.c` — exhaustive search for solutions of `x⁴ + y⁴ = zt(t² − z²)` over
  all `(z, t)` with `zt|t² − z²| ≤ 10¹⁴`: none found.
* `search/t6d.c`, `search/t6f.c`, `search/t6g.c` — searches over `(x, y)` for
  `x⁴ + xy³ + z⁴ + t⁴ = 0` testing the necessary divisor conditions: none satisfied.
* `search/goodm.c` — search for further "good `m`" for the Table 5 equation
  `y² + x²y + z²x − 2 = 0` (see above); only `m = 17, 553, 1241` for `c ≤ 3000`,
  `r ≤ 3·10⁵`, so the bound `4591` of `Table5.problem2_le_4591` was not improved.
### Conclusion (unchanged)
No open problem of the paper has been fully resolved.  All statements in the Lean
files are completely proved, and every partial result states its hypotheses
explicitly.
### Additional search (Table 8, Problem 5)
`search/t8.c` performs a meet-in-the-middle search for a nontrivial solution of
each of the five diagonal quartics of Table 8 (`11x⁴+4y⁴+2z⁴−t⁴ = 0` etc.) over
all `0 ≤ x, y, z, t ≤ 5000`.  No solution was found.  (Earlier local-solubility
checks, `search/loc4.c`, show that none of these equations has a congruence
obstruction, so a solution — if one exists — must simply be large.)
## The last two Table 6 equations (`RequestProject/Table6Quartic5.lean`)
Table 6 of the paper lists five homogeneous equations of size `H = 64` for which
Problem 3 (existence of a solution with all variables nonzero) is open.  Three of
them are treated in `Table6Quartic.lean`, `Table6Quartic2.lean`,
`Table6Quartic3.lean` and `Table6Quartic4.lean`.  The remaining two,
```
x⁴ − y³z + xyz² + xz³ = 0                                        (I)
x³z + xy³ + y²z² − yz³ = 0                                       (J)
```
are handled in `Table6Quartic5.lean`.  Both are smooth plane quartics, so they
have points over every completion (e.g. `(0 : 0 : 1)`) and no congruence
obstruction can exist; only coprimality results are within reach.
### Equation (I): no solution with `x ≠ 0`, `y ≠ 0`, `gcd(x, z) = 1`
`Table6.quarticI_no_solution_of_isCoprime_xz`.  Rewriting (I) as
`x⁴ = z (y³ − xyz − xz²)` shows `z ∣ x⁴`, so coprimality forces `z = ±1`; the
substitution `(x, y, z) ↦ (−x, −y, −z)`, which preserves (I), reduces to `z = 1`,
i.e. `x (x³ + y + 1) = y³`.  The two factors are coprime (a common prime `p`
would divide `y³`, hence `y`, hence `1`), so `x = s³`, `x³ + y + 1 = m³` and
`y = s m`.  This gives `m³ = s⁹ + s m + 1` with `s, m ≠ 0`, which is impossible:
writing `S = |s|`, `M = |m|`, the factorisation
`(m − s³)(m² + m s³ + s⁶) = s m + 1` together with `4(m² + m s³ + s⁶) =
(2m + s³)² + 3 s⁶` gives `3 S⁶ ≤ 4 S M + 4`, while the equation itself gives
`M³ ≤ S⁹ + S M + 1`; for `S ≥ 2` these are contradictory, and `S = 1` is checked
directly.  (`Table6.no_solution_cubic_nonic`.)
### Equation (J): no solution with `x, z ≠ 0`, `gcd(x, y) = gcd(y, z) = 1`
`Table6.quarticJ_no_solution_of_coprime`.  From
`z (x³ + y²z − yz²) = −x y³` and `IsCoprime y (x³ + y²z − yz²)` one gets
`y³ ∣ z`, so `gcd(y, z) = 1` forces `y = ±1`.  Both signs reduce (again via
`(x, y, z) ↦ (−x, −y, −z)`) to `x³z + x + z² − z³ = 0`, which has no solution with
`x z ≠ 0`: the equation gives `z ∣ x`, and substituting `x = z v` and dividing by
`z` yields `v (1 + z³v²) = z² − z`; taking absolute values gives
`|v|(|z|³|v|² − 1) ≤ |z|² + |z|`, whence `|z|³ − 1 ≤ |z|² + |z|` and so `|z| = 1`.
The two remaining cases `z = ±1` are immediate.  (`Table6.quarticJ_core`.)
### What is still missing
Both equations are homogeneous, so a hypothetical all-nonzero solution can only
be normalised by `gcd(x, y, z) = 1`, which does not give the pairwise
coprimality used above.  Problem 3 therefore remains open for (I) when
`gcd(x, z) > 1`, and for (J) when `gcd(x, y) > 1` or `gcd(y, z) > 1`.
### Searches performed
Brute-force searches over `|x|, |y|, |z| ≤ 120`, root-finding searches over
`|y|, |z| ≤ 300`, and searches of the reduced curves up to `3·10⁶` found no
nontrivial solution of either equation.  (These are exploratory computations, not
machine-verified statements.)
## Full reductions of the remaining Table 6 equations (`Table6Quartic6/7/8.lean`)
The three files complete the analysis of Table 6 begun above by replacing the
open Problem 3 instances with *exactly equivalent* three-monomial equations.
* `Table6.quarticG_iff_reduced` (`Table6Quartic8.lean`).  The equation
  `x⁴ + x³y + xy³ − z⁴ = 0` has a solution with all variables nonzero **iff**
  `w³ + a⁸w + a¹² = b⁴` has one with `a, w, b ≠ 0`.  The reduction combines the
  descent to a coprime solution (`quarticG_exists_coprime_solution`) with the
  fourth-power factorisation `x · (x³ + x²y + y³) = z⁴`.
* `Table6.quarticI_iff_reduced` (`Table6Quartic6.lean`).  Equation (I)
  `x⁴ − y³z + xyz² + xz³ = 0` reduces to `m³ = e r⁹ + e t⁵ r m + t⁹`.
* `Table6.quarticJ_iff_reduced` (`Table6Quartic7.lean`).  Equation (J)
  `x³z + xy³ + y²z² − yz³ = 0` reduces, for `gcd(y, z) = 1`, to
  `z⁵v³ + c⁷v + c³ = z`.  In addition
  `Table6.quarticJ_no_solution_of_isCoprime_yz_of_same_sign` rules out all
  solutions with `y z > 0`.
The corresponding rational-point corollaries (`quarticI_rational_point`,
`quarticJ_rational_point`) record that the reduced curves have no nontrivial
rational point in the ranges covered by the algebraic argument.
## Powerful values of polynomials (`PowerfulNumbers.lean`, `CubeSquareValues.lean`)
Table 13 of the paper lists several equations of the shape `x^a y^b = f(z)` for
which **Problem 6** (existence of an integer solution) is open, including
equation (27) `x³y² = z³ + 6`, the smallest three-monomial equation of unknown
solvability.
`PowerfulNumbers.lean` proves the two arithmetic characterisations that make
these equations tractable:
* `exists_cube_mul_sq_iff` — a nonzero integer is of the form `x³y²` **iff** it
  is *powerful* (every prime divisor divides it at least twice);
* `exists_pow_four_mul_cube_iff` — a nonzero integer is of the form `x⁴y³`
  **iff** no prime divides it exactly once, twice or five times (the exponents
  not of the form `4a + 3b`).
`CubeSquareValues.lean` applies these to obtain *exact reformulations* of the
open equations,
* `problem6_cubic_add_six_iff`      : `x³y² = z³ + 6` ↔ some `z³ + 6` is powerful;
* `problem6_quartic_add_two_iff`    : `x³y² = z⁴ + 2` ↔ some `z⁴ + 2` is powerful;
* `problem6_quartic_sub_three_iff`  : `x³y² = z⁴ − 3` ↔ some `z⁴ − 3` is powerful;
* `problem6_sq_add_three_iff`       : `x⁴y³ = z² + 3` ↔ some `z² + 3` has no
  prime of multiplicity `1`, `2` or `5`,
together with congruence obstructions constraining any hypothetical solution:
for `x³y² = z⁴ + 2`, `z` must be odd with `z mod 9 ∈ {0, 2, 3, 6, 7}`; for
`x³y² = z⁴ − 3`, `z` must be even and not divisible by `3`; for
`x³y² = z³ + 6`, `z` must be odd and not divisible by `3`; for `x⁴y³ = z² + 3`,
`z` must be even and not divisible by `3`.
These are constraints, not impossibility proofs.  A finite congruence
obstruction cannot exist for this family: Hensel lifting always leaves surviving
residues modulo every prime power, so the mod-`p` conditions can never be
combined into a contradiction.
### Searches performed
`search2/xy43.c` enumerates all pairs `(x, y)` with `x⁴y³ ≤ 10²⁴` (about
`3.6 · 10⁸` pairs) and tests whether `x⁴y³ − C` is a square.  For `C = 3` no
solution at all was found; for `C = 1` only `(1, 1, 0)` and for `C = −1` only
`(1, 2, 3)`.  `search2/sieve.c` sieves the values `f(z)` for
`f ∈ {z⁴+2, z⁴−3, z⁴+1, z³+6, z³+2, 2z³+1, z³−z+1, z³+z+1}`, stripping all
primes up to `10⁵` and testing the cofactor: no powerful value of `z⁴ + 2` or
`z⁴ − 3` occurs for `|z| ≤ 10⁶`, and `z⁴ + 1` is powerful only for `z = 0`.
(These are exploratory computations, not machine-verified statements.)
## Session 4: function-field (polynomial) analogues — `FunctionField.lean`, `FunctionFieldPowerful.lean`
A positive answer to Problems 2, 4, 6 or 7 for a given equation is very often obtained by
exhibiting a **polynomial identity**: a parametric family `x(t), y(t), z(t)` of solutions.
The two new files prove, unconditionally and for a long list of the paper's open equations,
that **no such family exists**: over any field of characteristic zero, every polynomial
solution is constant (up to the degenerate families listed explicitly).
The engine is the Mason–Stothers theorem (`Polynomial.abc` in Mathlib).
### `RequestProject/FunctionField.lean`
* `FunctionField.constant_of_pow_mul_pow_eq`.  If `a x^p y^q = b z^r + c` holds in `k[X]`
  with `a, b, c` nonzero constants, `p, q, r ≥ 2` and `x, y ≠ 0`, then `x`, `y`, `z` are all
  constant.  Proof: with `A = a x^p y^q`, `B = -b z^r`, `C = -c` one has `A + B + C = 0`,
  `A + B` is a unit (hence `A, B` coprime), and
  `rad(ABC) ∣ rad x · rad y · rad z`, so Mason–Stothers yields both `X + Y + 1 ≤ Z` and
  `Z + 1 ≤ X + Y`; the derivative branch forces all degrees to vanish.
* Corollaries: all four equations of **Table 13** (`x³y² = z³+6`, `z⁴+2`, `z⁴−3`,
  `x⁴y³ = z²+3`, Problem 6 open) and the **Table 12** equations `x³y² = z⁴+1`, `z³+2`,
  `2z³+1`, `x⁴y³ = z²+1` (Problem 4 open).  `cubeAddSix_eq_C` restates the flagship case
  over `ℚ` as "`x`, `y`, `z` are constant polynomials".
* **Table 11** (Problems 2 and 7 open).  Using the reductions of `Table11.lean` together with
  "coprime factors of an `n`-th power in `k[X]` are `n`-th powers up to a constant", each of
  `y(x³ − z²) = z`, `y(x³ − z²) = x` and `x²y² + x = z³` reduces to an instance of the main
  theorem; the results `eqC_polynomial_constant`, `eqA_polynomial_constant`,
  `eq11b_polynomial_constant` state that every polynomial solution is constant apart from the
  degenerate families (`z = 0` with `y = 0` or `x = 0`; `x = 0` with `y = 0` or `z = 0`;
  `x = z = 0` or `y = 0, x = z³`), which are genuine and cannot be dropped.
### `RequestProject/FunctionFieldPowerful.lean`
Handles the two remaining Table 12 equations whose right-hand side is not of the form
`b z^r + c`:
* `natDegree_succ_le_radical_pair` — Mason–Stothers for a pair of shifts: for `r ≠ s` and
  nonconstant `z`, `deg z + 1 ≤ deg rad(z − r) + deg rad(z − s)`.
* `constant_of_powerful_eq_pow_add_const` — the general form of the main theorem of
  `FunctionField.lean`: if `P` is powerful (`2 deg rad P ≤ deg P`) and `P = b z^r + c` with
  `r ≥ 2` and `b, c ≠ 0` constants, then `z` and `P` are constant.
* `constant_of_powerful_of_three_distinct_roots` — if `2 deg rad P ≤ deg P` (i.e. `P` is
  *powerful*) and `P = c (z − ρ₁)(z − ρ₂)(z − ρ₃)` with distinct `ρᵢ`, then `z` is constant.
  Summing the three pair estimates gives `3 deg z + 3 ≤ 2 deg rad P ≤ deg P = 3 deg z`.
* `constant_of_pow_mul_pow_eq_separable_cubic` — over an algebraically closed field of
  characteristic zero, `x^p y^q = f(z)` with `p, q ≥ 2` and `f` a monic separable cubic forces
  `x`, `y`, `z` constant.
* `cubeSubXAddOne_constant`, `cubeAddXAddOne_constant` — the Table 12 equations
  `x³y² = z³ − z + 1` and `x³y² = z³ + z + 1` have no nonconstant polynomial solutions
  over `ℚ` (obtained by base change to `ℂ`, where the cubics split; separability is certified
  by explicit Bézout coefficients, the discriminants being `−31` and `−23`).
These results do **not** settle any of the open problems: they exclude one (very common) way
of answering them positively.  The method does not cover the Table 11 equation
`y(x³ − z²) = x + 1`, the Table 5 equation `y² + x²y + z²x = 2`, or equation (19)
`x⁴ + y³ + z² + 1 = 0` (for the latter `1/4 + 1/3 + 1/2 > 1`, so Mason–Stothers gives no
contradiction).
### Searches performed in this session (exploratory, not machine-verified)
* `search/t5poly.c`, `search/t5fam2.c`: exhaustive search for polynomial families of the
  Table 5 equation `y² + x²y + z²x = 2` in both parametrisations and many degree/coefficient
  ranges — none found.
* `search/t5good.c`: the "good `m`" of the Table 5 analysis up to `2·10⁶`
  (17, 31, 49, 71, 79, 97, 127, 142, …, 83407); all their prime factors are `≡ ±1 mod 8`.
* `search/t11fam.c`, `search/t11sym*.py`: families for `y(x³ − z²) = x + 1`; the minimal
  degree case was ruled out symbolically, brute force found nothing (the classical near-miss
  is `x = t² + 3`, `z = t³ + 9t/2`, `y = 4/27`, with non-integral `y`).
* `search/eq19*.c`, `search/eq19*.py`: equation (19) `x⁴ + y³ + z² + 1 = 0`.  Integer
  solutions found for `|x| ≤ 1500` are sporadic — `(0,−1,0)`, `(1,−3,5)`, `(6,−13,30)`,
  `(11,−27,71)`, `(29,−5507,408669)`, `(31,−147,1501)`, `(51,−203,1265)`,
  `(288,−16957,2206566)`, `(1386,−15661,388458)`, … — and the degree pattern `(1,2,3)` for a
  polynomial family was ruled out over `ℚ` by a Gröbner computation.
* `search/t13a.c`: the two-variable Table 13 equation `2y³ + xy + x⁴ + 1 = 0` has no integer
  solution with `|x| ≤ 2·10⁷`, and no congruence obstruction exists modulo any `m < 400`.
