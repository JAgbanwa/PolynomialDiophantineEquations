This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Summary of changes for run 3bdc1389-2921-4f70-8e76-2f5c22663dcc
The paper's claim is correct, and its proof is sound: I checked every step and then formalized the whole argument in Lean, with no `sorry`, no added axioms, and a clean build with no errors or warnings.

Result (in `RequestProject/Main.lean`):

- `no_integer_solution : ¬ ∃ x y : ℤ, y ^ 3 + y ^ 2 + x * y = x ^ 4 + 1` — the main theorem.
- `divisor_of_sq_add_self_add_one_mod_three` — the paper's lemma: for any integer `u`, every positive divisor `d` of `u² + u + 1` with `3 ∤ d` satisfies `d ≡ 1 (mod 3)`. Proved by strong induction on `d` via its prime factors.
- `prime_dvd_sq_add_self_add_one_mod_three` — the prime case: a prime `p ≠ 3` dividing `u² + u + 1` satisfies `p ≡ 1 (mod 3)`. Proved by showing the image of `u` in `ZMod p` is a unit of order exactly 3, so `3 ∣ p − 1`.

Each step of the paper is reflected in the formal proof:
1. The exact identity `(x² + y)·(x⁴ − x²y + y² − x² + y + x) = (x³)² + x³ + 1` under the equation, together with positivity of `(x³)² + x³ + 1`.
2. Reduction mod 3, which forces `x ≡ 1`, `y ≡ 2 (mod 3)`, hence the complementary factor `B ≡ 2 (mod 3)` and in particular `3 ∤ B`.
3. The sign check: `A = x² + y < 0` would force `y < 0` while `y² + y + x ≥ 0`, contradicting `y·(y² + y + x) = x⁴ + 1 > 0`; so `A > 0` and therefore `B > 0`.
4. Applying the divisor lemma with `u = x³` to the positive divisor `B` gives `B ≡ 1 (mod 3)`, contradicting `B ≡ 2 (mod 3)`.

The work is committed and pushed.
