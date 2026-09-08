This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Summary of changes for run 0836b71d-ec8d-4f5c-914a-569abde27473
**Verdict: the paper's claim is true**, and its proof is correct as written. I checked every step of the argument and then formalised it in Lean; the project builds cleanly with no `sorry`, no `admit`, no errors and no warnings, and `DiophantineY3XY.no_solutions` depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

All of the paper's computational claims verify exactly:
- `(y − 1)(y² + y + 1 + x) = x⁴ + 2 = (x²)² + 2·1²` (using the equation);
- with `ℓ = 2x − 13`, `(y − ℓ)(y² + yℓ + ℓ² + x) = (x² − 4x + 20)² + 2(7x − 30)²`;
- `49A = B(7x + 2) + 1040` and `12C = 3(2y + 2x − 13)² + 4(3x − 19)² + 77`;
- the exceptional primes `5` and `13` really are eliminated by the square-residue checks, and modulo 8 the equation does force `D·C ≡ 7`.

The one place the write-up is loose is the positivity paragraph (the displayed chain `y³ + xy = v(u − v²) ≤ u(u − 1) < u⁴ − u + 3` is stated with a mismatched intermediate bound). The conclusion `y > 1` is nevertheless correct, and I proved it in Lean via the clean bound `v(u − v²) ≤ (u − 1)²  <  u⁴ − u + 3` for `u ≥ v² + 1`, `v ≥ 1`.

**What is in the project** (`RequestProject/Main.lean`):
- `DiophantineY3XY.prime_mod_eight_of_dvd_sq_add_two_sq` — Lemma 1: an odd prime dividing `a² + 2b²` but not `b` is `≡ 1, 3 (mod 8)` (via `-2` being a quadratic residue exactly for such primes).
- `DiophantineY3XY.mod_eight_of_forall_prime_dvd` — second half of Lemma 1: a nonzero natural number whose prime divisors are all `≡ 1, 3 (mod 8)` is itself `≡ 1, 3 (mod 8)`; plus its integer/`ZMod 8` form.
- Supporting steps: positivity of `x⁴ + x + 3`, `y ≥ 2`, positivity of `C`, and the fact that an odd prime divisor of `1040` is `5` or `13`.
- `DiophantineY3XY.no_solutions` — the main theorem: `¬ ∃ x y : ℤ, y³ + xy = x⁴ + x + 3`.

The original PDF is left untouched in the project.
