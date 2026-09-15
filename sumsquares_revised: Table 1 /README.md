This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```


# Summary of changes for run ad8e12d9-28db-4acf-b290-f3b0f8e3acfb
I worked on all eighteen equations of Table 1 of the paper (`On_the_polynomial_values_represented_by_quadratic_forms.pdf`), which the authors list as the length-9 Diophantine equations whose finiteness problem is still open after their work.

**Honest bottom line first: I did not resolve any of the eighteen.** I attacked them hard — searching for infinite families via algebraic identities (polynomial parametrisations of the solution surfaces, Hall-type identities `(t²+2c)³ − (t³+3ct)² = c²(3t²+8c)`, factorisations such as `(t²+t−4)³ − 2 = (t³−6t+6)(t³+3t²−3t−11)`), via the paper's Pell/tangent-line machinery, via Vieta jumping on `x²y + y²z + z²x = 1`, and searching for finiteness arguments — and also ran extensive numerical searches (for instance all solutions of `x²y+y²z+z²x=1` with coordinates up to several thousand). Every one of these equations reduces to a recognised hard problem (Hall/Pillai-type gaps, powerful values of cubic and quartic polynomials, or rational points on curves of genus ≥ 2 requiring effective Faltings-type methods), so all eighteen remain open; I have not claimed otherwise anywhere in the project.

**What is delivered:** one self-contained Lean file per equation, `RequestProject/Table1Eq01.lean` … `RequestProject/Table1Eq18.lean`. Each imports only `Mathlib`, lives in its own namespace, and compiles with no `sorry`, no `axiom`, no `native_decide`, and no warnings; the whole project builds cleanly. Each file states the equation and proves unconditional facts about its integer solution set: verified explicit solutions; symmetries; equivalent reformulations and solvability criteria (divisor and discriminant criteria for the `z² + y²z + …` family, Hall-type form for `x⁴+y³+z²+1=0`, divisibility of the right-hand side by the Hall difference `x³−z²` for the `y(x³−z²)=…` family, powerfulness of the right-hand side for the `x³y²=…` family); complete resolutions of natural sub-families (one variable set to `0` or `±1`, e.g. the only solutions of `x³y² = z³+2` with `y=±1` are `(1,±1,−1)`, and the `y=±1` solutions of `x³y² = z³∓z+1` are determined completely by a cube-sandwich argument); congruence obstructions proved by finite checks in `ZMod n` (e.g. `6 ∣ y` for equation 2, `x ≡ 1 (mod 8)` for `x³y² = z⁴+1`, `y ≡ 2 (mod 3)` for `x⁴+xy+y³+1=0`); arithmetic constraints on prime divisors (every odd prime dividing `xy` is `≡ 1 mod 8` for `x³y² = z⁴+1`, and `≡ 1 mod 4` for `x⁴y³ = z²+1`); pairwise coprimality of the coordinates for `x²y+y²z+z²x=1`; and kernel-checked complete enumerations of all solutions inside explicit boxes (`[-20,20]³` for the three-variable equations, `[-60,60]²` for the two-variable ones).

`TABLE1_STATUS.md` gives an equation-by-equation index of the files and their contents, and states plainly that the finiteness question for all eighteen is still open.


# Table 1 of *On the polynomial values represented by quadratic forms*

Table 1 of the paper lists **eighteen** Diophantine equations of length `l = 9` for which
Problem 1.1 (decide whether the integer solution set is finite or infinite, and in the finite
case list all solutions) remains **open** after the paper.  This project contains one
self-contained Lean 4 file per equation, each proving unconditional facts about the
corresponding integer solution set.  Every file compiles with no `sorry`, no `axiom`,
no `native_decide`, and no warnings.

## Honest status

None of the eighteen equations is resolved here: after a substantial search for infinite
solution families (algebraic identities, Pell-type constructions, Vieta jumping, Hall-type
identities) and for finiteness arguments, no unconditional resolution of any of these
problems was obtained, and the finiteness question for all eighteen remains open.
The files therefore record what *can* be proved unconditionally today:

* verified explicit solutions;
* symmetries of the solution sets;
* equivalent reformulations and solvability criteria (e.g. divisor/discriminant criteria);
* complete resolutions of natural sub-families (one variable fixed to `0` or `±1`);
* congruence obstructions, each proved by a finite check in `ZMod n`;
* complete, kernel-checked enumerations of the solutions inside an explicit box.

## Files

| # | Equation | Lean file (namespace) | Highlights |
|---|----------|----------------------|------------|
| 1 | `z² + y²z + x³ − 2 = 0` | `Table1Eq01` | factorisation criterion, discriminant criterion, no solution with `z = 0`, `x % 4 ≠ 3`, `x % 5 ≠ 4`, `z % 4 ≠ 0`, box `[-20,20]³` |
| 2 | `z² + y²z + x³ − x − 1 = 0` | `Table1Eq02` | `6 ∣ y`, `z` odd, criteria, no solution with `z = 0`, box `[-20,20]³` |
| 3 | `z² + y²z + x³y + 1 = 0` | `Table1Eq03` | discriminant criterion, the two solutions with `z = 0`, `x` odd, `3 ∤ y`, `4 ∤ y`, box `[-20,20]³` |
| 4 | `x²y + y²z + z²x = 1` | `Table1Eq04` | cyclic symmetry, pairwise coprimality, Vieta second-root map, large solutions, box `[-20,20]³` |
| 5 | `x⁴ + y³ + z² + 1 = 0` | `Table1Eq05` | Hall-type form `(−y)³ − z² = x⁴ + 1`, `y ≤ −1`, `y % 8 ∈ {3,5,7}`, box `[-20,20]³` |
| 6 | `y(x³ − z²) = x² + 1` | `Table1Eq06` | divisibility structure, solutions with `z = 0` and with `x = 0`, `3 ∤ y`, `4 ∤ y`, box `[-20,20]³` |
| 7 | `y(x³ − z²) = 2x − 1` | `Table1Eq07` | divisibility structure, solutions with `z = 0` and `x = 0`, `y` odd, `y % 3 ≠ 2`, box `[-20,20]³` |
| 8 | `y(x³ − z²) = 2x + 1` | `Table1Eq08` | divisibility structure, solutions with `z = 0` and `x = 0`, `y` odd, box `[-20,20]³` |
| 9 | `x³y² = z³ + 2` | `Table1Eq09` | `z³+2` powerful, all solutions with `y = ±1` (only `(1,±1,−1)`), all variables odd, box `[-20,20]³` |
| 10 | `x³y² = z³ − z + 1` | `Table1Eq10` | `z³−z+1` powerful, all solutions with `y = ±1`, `x ≡ 1 (mod 3)`, `x,y` odd, box `[-20,20]³` |
| 11 | `x³y² = z³ + z + 1` | `Table1Eq11` | `z³+z+1` powerful, all solutions with `y = ±1`, `x,y` odd and prime to `7`, box `[-20,20]³` |
| 12 | `x³y² = 2z³ + 1` | `Table1Eq12` | `2z³+1` powerful, all solutions with `z = 0`, `x,y` odd, `y ≡ ±1 (mod 9)`, box `[-20,20]³` |
| 13 | `x³y² = z⁴ + 1` | `Table1Eq13` | `x ≡ 1 (mod 8)`, `y` odd, `z` even, all solutions with `x = 1`, every odd prime divisor of `xy` is `≡ 1 (mod 8)`, box `[-20,20]³` |
| 14 | `x⁴y³ = z² + 1` | `Table1Eq14` | `y ≥ 1`, cube-powerfulness of `z²+1`, odd prime divisors of `xy` are `≡ 1 (mod 4)`, all solutions with `y = 1`, box `[-20,20]³` |
| 15 | `y³ − y = x⁴ − x` | `Table1Eq15` | near-uniqueness of `y`, diagonal solutions, `x % 9 ∈ {0,1,3,4,6,7}`, `y % 5 ≠ 2`, box `[-60,60]²` |
| 16 | `y³ + y = x⁴ + x` | `Table1Eq16` | uniqueness of `y` for given `x`, diagonal solutions, `y % 9 ∈ {0,1,3,4,6,7}`, box `[-60,60]²` |
| 17 | `x⁴ + xy + y³ − 1 = 0` | `Table1Eq17` | solutions with `x = 0` and `y = 0`, `y % 4 ≠ 2`, `3 ∣ x → 9 ∣ x`, box `[-60,60]²` |
| 18 | `x⁴ + xy + y³ + 1 = 0` | `Table1Eq18` | solution with `x = 0`, no solution with `y = 0`, `y ≡ 2 (mod 3)`, `x % 3 ≠ 2`, box `[-60,60]²` |

Here "`P` is *powerful*" means that every prime dividing `P` divides it at least twice; this
is exactly the constraint that the shape `x³y²` imposes on the right-hand side, and it is the
form in which equations 9–13 should be attacked.

Each file is independent: it imports only `Mathlib` and lives in its own namespace, so it can
be compiled on its own (for example in the online Lean editor).
