# Summary of changes for run 902435c5-45f1-4f8d-9a17-34fea49dba93
I added two further pieces of Section 4 of the paper to `RequestProject/Main.lean`, both fully proved with no `sorry`/`admit`/`axiom` (each depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`). The whole module builds cleanly.
1. Non-multiplicativity of `2y² + yz + 2z²`.
   - `MultiplicativeForm`: a definition of a multiplicative binary quadratic form (if it represents positive `m` and `n`, it represents `m·n`).
   - `form2_represents_two`: the form represents `2` (via `F(0,1) = 2`).
   - `form2_not_represents_four`: the equation `2y² + yz + 2z² = 4` has no integer solutions (bounded via the identity `2·F − 3(y²+z²) = (y+z)²`, then a finite case check).
   - `form2_not_multiplicative`: hence `2y² + yz + 2z²` is not multiplicative — it represents `2` but not `2·2 = 4`.
2. The degenerate quadratic-form case `Δ = 0` (near the end of Section 4).
   - `degenerate_factorization`: if `B² − 4AC = 0` then `(A,B,C) = (k n², 2 k n m, k m²)` for some integers `k, n, m`.
   - `degenerate_reduces`: given that factorisation, `A y² + B y z + C z² = k (n y + m z)²`.
   - `degenerate_infinite_iff`: for non-trivial `(n,m)`, the equation `k (n y + m z)² = P(x)` has infinitely many integer solutions `(x,y,z)` iff the reduced equation `k t² = P(x)` has a solution `(x₀,t₀)` with `gcd(n,m) ∣ t₀` (paper's eq. (33) criterion), proved by extracting one solution in the forward direction and building an explicit injection `ℤ → solutions` in the backward direction.
   - `degenerate_case`: the same equivalence stated directly for `A y² + B y z + C z² = P(x)`.
The module docstring's "Main results" list was updated to mention the new results. All work is committed and pushed.
# Summary of changes for run 9aaebb4a-34bb-40c2-8e01-1a6b929c0a00
I fixed the three reported issues in `RequestProject/Main.lean` (the file the reported `MathlibDemo.lean` line numbers correspond to). The whole file still builds cleanly with no `sorry`/`admit`/`axiom`, and the affected results depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
1. `grind` failure (the tangent-construction identity in `prop_4_1_solution`). The final algebraic goal `R u^2 * F(...) = R u^2 * R(Q x)` was being closed by the fragile `grind +qlia`. I replaced it with a deterministic, version-independent proof: after cancelling `R u^2`, I cancel a further explicit factor `4` (so the divisibility relations `hlam`/`hmu`, which each carry a factor `2 * R u`, can be substituted without any division) and then discharge the identity with an explicit `linear_combination` of `hlam`, `hmu`, the auxiliary equation `h27`, the form value `hm`, and the Taylor expansion `hTaylor (Q x)`. The exact combination coefficients were derived by hand and verified by `ring`.
2. The two `ring_nf` "made no progress" warnings (the period/congruence step of `algorithm_4_3` feeding `prop_4_2`). These came from a `convert ... using 1 ; ring` pattern whose trailing `ring` could become a no-op. I rewrote both divisibility goals directly: rewrite the shifted expression as `(original) ± 2 * R u * (...)` via `ring`, then close with `dvd_add`/`dvd_sub` and `2 * |R u| ∣ 2 * R u`, removing the brittle `convert`/`ring` dependency.
3. The `norm_num at this` "does nothing" warning (in the `hX_div` step). The `norm_num` call was redundant, so I removed it; the surrounding `obtain`/`exact` argument goes through unchanged.
All changes are committed and pushed. I verified the module builds (`RequestProject.Main`), contains no `sorry`/`admit`/`axiom`, and that the touched theorems check against only the standard axioms.
# Summary of changes for run 4766a9e2-fb99-46f0-b202-a3c89a764586
I extended `RequestProject/Main.lean` so that the whole of the paper's Section 4 machinery is now fully formalised, with no `sorry`, `admit`, or `axiom`. The project builds cleanly and every result depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`; the Section 3 results additionally use `Lean.ofReduceBool`/`Lean.trustCompiler` from `native_decide`).
Status of the requested items:
Already fully formalised (verified intact and building):
- Proposition 3.1 (`prop_3_1`), Proposition 3.2 (`prop_3_2_eq14/15/16/17`), Proposition 4.4 (`prop_4_4a`, `prop_4_4b`).
Newly completed:
- Proposition 4.1 (`prop_4_1`): previously only the algebraic identity was present (now kept as `prop_4_1_core`). Added the full statement: for a non-degenerate form `F(y,z)=Ay²+Byz+Cz²`, if the auxiliary equation (27) together with the congruences (28) has infinitely many solutions, then `F(y,z)=R(Q(x))` is solvable for infinitely many `x`. Proved via the tangent construction (`prop_4_1_solution`) plus a finite-fibre infinitude argument.
- Proposition 4.2 (`prop_4_2`): the auxiliary equation (30) `a x²+b x+c = −D v²` under a period-`2m` congruence condition has infinitely many solutions in the prescribed class, under exactly the paper's conditions (a)–(c). (The paper's non-degeneracy `Δ≠0` is a standing Section-4 assumption and is not among Proposition 4.2's own hypotheses, so it is not required here; this is noted in the docstring.)
- Algorithm 4.3 (`algorithm_4_3`) and Algorithm 2.2 (`algorithm_2_2`), each stated as a theorem whose hypotheses record the data produced by the algorithm's search steps, and proved as the composition of the propositions (Algorithm 2.2 is the sum-of-two-squares recipe via property (*); note the paper numbers this recipe 2.2 — there is no Algorithm 2.1).
- The full "infinitude/congruence machinery": a residue-controlled generalised Pell theorem (`genPell_infinite_cong`) giving infinitely many solutions of `v²=a x²+c` in any prescribed residue class modulo `N`, together with its supporting lemmas (existence of a unit power congruent to the identity mod `N` via a finite-order argument, norm/congruence preservation of the Pell iteration, and injectivity of the iteration via the real quantity `v+x√a`). General helpers `infinite_fst_of_finite_fibers` and `finite_setOf_mul_sq_eq` were also added.
Everything is in the single file `RequestProject/Main.lean`. I also updated the module docstring's "Main results" list, removed one genuinely unused hypothesis, and cleaned up leftover tactic artefacts so the build is free of warnings and stray messages.
# Summary of changes for run 60b0aaad-6024-4784-b330-d282bb0b4653
I fixed the reported type mismatch. The error `Sum2Sq (x ^ 6 + -4)` vs `Sum2Sq (x ^ 6 - 4)` came from a step that relied on `simpa` to reconcile `x^6 + -4` with `x^6 - 4`; on your Lean/Mathlib version that normalization didn't happen, leaving the mismatch.
In `RequestProject/Main.lean` I made the affected steps version-robust:
- In `odd_pow6_sub4_S2_infinite`, I replaced the `simpa`-based reconciliation with an explicit `rw [sub_eq_add_neg]; exact this` (and passed the positivity hypothesis in the exact `x^6 + (-4)` form via a `linarith` step), so the conversion no longer depends on simp behavior.
- I applied the same robust pattern to the analogous `-3` case in `even_pow6_sub3_S2_infinite`, which previously relied on definitional equality between `- 3` and `+ -3`.
The project builds cleanly (`RequestProject.Main`) with no `sorry`, `admit`, or `axiom`. Changes are committed and pushed.
# Summary of changes for run cfa3ebbe-1238-4abe-8ffc-c883c70bbb14
I formalised the paper *On the polynomial values represented by quadratic forms* (Grechuk–Agbanwa) as a single self-contained Lean file, `RequestProject/Main.lean`. It builds cleanly with no `sorry`, `admit`, or `axiom`; the main theorems depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`, plus `Lean.ofReduceBool`/`Lean.trustCompiler` from `native_decide` used to certify the non-square coefficients).
What is formalised:
Section 2 (sum-of-two-squares machinery):
- `Sum2Sq` (integer sums of two squares), multiplicativity `Sum2Sq.mul` (Brahmagupta–Fibonacci), and the hard "division" direction of property (*), `Sum2Sq.div`: if `a` and `a·b` are sums of two squares (`a,b>0`) then so is `b`. This is proved via the prime-factorisation characterisation (`natS2_iff_valuation`, built on Mathlib's `Nat.eq_sq_add_sq_iff`) and a p-adic valuation parity argument (`natS2_div`).
- `not_sum2sq_mod4_three`: no integer ≡ 3 (mod 4) is a sum of two squares.
- `genPell_infinite`: the generalised Pell equation `v² = a x² + c` (with `a>0` non-square, `c≠0`, one solution) has infinitely many positive solutions — proved from scratch by iterating multiplication by a fundamental unit (`pellStep`/`pellIter`, `pell_unit`, `pell_base`, `pellIter_inv`, `pellIter_fst_lt`), giving a strictly increasing sequence of solutions. This is the paper's appeal to Gauss's theorem [9, Prop. 5.4].
- `sum2sq_x6_add`: the core tangent identity showing `x⁶ + f` is a sum of two squares whenever the auxiliary Pell equation `v² = 4(u³+f)x² − u(u³−8f)` is solvable and `R(u)=u³+f` is a positive sum of two squares.
Section 3 (the shortest open equations):
- `prop_3_1`: `y² + x³y + z² + 1 = 0` (equation (2)) has infinitely many integer solutions — the paper's main application, using `f=-4, u=162` and the explicit base solution given in the paper.
- `prop_3_2_eq14/15/16/17`: the four further length-9 equations (14)–(17) each have infinitely many integer solutions, using `f ∈ {8,5,-3}` and, for (17), the factorisation `(x³+1)²−4 = (w⁶−3)(w⁶+1)` with `x=-w²`.
These rest on decomposition lemmas (`sol_31`, `sol_14`–`sol_17`, `odd_of_S2_sub4`) that recover explicit `y,z` from a representation `x⁶+f = A²+B²` via parity analysis, and on infinitude lemmas assembling `genPell_infinite` with the tangent identity.
Section 4 (general binary quadratic forms):
- `prop_4_1`: the algebraic core of the tangent construction for an arbitrary form `A y² + B y z + C z²`.
- `prop_4_4a`, `prop_4_4b`: the non-multiplicative-form equations `2y² + yz + 2z² = x³ ± 1` have infinitely many integer solutions, via the explicit polynomial families given in the paper (verified by `ring`).
Each result is stated as an `.Infinite` statement about the corresponding integer solution set, faithful to the paper's claims. All work is committed and pushed.
