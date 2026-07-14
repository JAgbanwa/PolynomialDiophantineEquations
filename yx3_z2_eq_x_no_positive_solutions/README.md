# Extra attempts at verification
I made further attempts at stress-testing the correctness of these results by asking this specific question in three different windows of ChatGPT 5.5 Pro:

```
This paper claims to describe all integer solutions to z² - x·y² = x³ + 2. How true is this statement? Rigorously verify such claim, let's see!
```

and the outcome is found here: [\[1\]](https://chatgpt.com/c/6a5681e5-9254-83eb-959a-2abdb0d452a8), [\[2\]](https://chatgpt.com/c/6a5681dc-baf4-83eb-b941-528d01b5aeb4) and [\[3\]](https://chatgpt.com/c/6a5681ab-b460-83eb-bdb9-0c54cc0861ce).


# Summary of changes for run 0fc0490a-df7a-4d1f-b6b0-12d68ceed60b
The Lean formalization in `RequestProject/Main.lean` (namespace `LjunggrenNagellReduction`) is now complete and sorry-free: the project builds cleanly with no warnings, and every proved result depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). I verified this with a full build, a project-wide search confirming no `sorry`/`admit`/`axiom`/`native_decide`, and `#print axioms` on the main results.
What was completed this session:
- The file previously had no active `sorry`, but the appendix's full Gaussian-integer factorization (Proposition A.1, existence part) was left unproven inside a comment block. I have now formalized and proved it in full, so all of the paper's own content is machine-checked.
- Added and proved a reusable engine lemma `gauss_extract`: for a Gaussian integer `w` coprime to its conjugate, if `(M : ℤ[i])^k ∣ w · conj w` with `M ≥ 1` and `k ≠ 0`, then the `M`-part splits off as a perfect `k`-th power dividing `w`, with norm exactly `M`. The proof avoids explicit per-prime bookkeeping by combining the decomposition-monoid divisor split, the Bézout-domain "coprime product equal to a power" lemma, and a conjugation/norm symmetry argument that pins the norm exactly.
- Proved `prop_A1` using `gauss_extract` twice (peeling off the fourth power from `A`, then the cube from `B`): if `U² + 1 = A⁴B³` with `U, A, B ≥ 1`, then there exist Gaussian integers `α, β` and a unit `ε` with `U + i = ε·α⁴·β³`, `N(α) = A`, `N(β) = B`.
- Added a small helper `gauss_norm_associated` (associated Gaussian integers have equal norm) and cleaned up all linter and `ring` suggestion warnings.
Status of the overall result: the main chain (Lemmas 2.1–2.3, Theorem 3.1 `only_solution`, Corollary 3.2 `no_positive_solution`) and the entire Appendix A are fully proved. As in the paper itself, the single external ingredient — Theorem 1.1, the classical Ljunggren–Nagell statement that `U² + 1 = A⁴B³` has no positive solution — is carried as an explicit, clearly-documented hypothesis (`LjunggrenNagell`), stated as an honest `Prop` (not an axiom). The paper deliberately cites rather than proves this deep result (it is not available in Mathlib), so keeping it as a hypothesis is the faithful formalization of "the results of this paper"; everything the paper actually proves is now formalized with no gaps.
# Summary of changes for run 1e158de0-8853-4381-959e-def9e65d5d0d
I formalised the results of the paper "A Ljunggren–Nagell reduction" in Lean 4 (Mathlib), in `RequestProject/Main.lean`, namespace `LjunggrenNagellReduction`. The file builds cleanly with no `sorry` in any active code, and all proved results depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
What is formalised and fully proved:
- `LjunggrenNagell` (Theorem 1.1, the external Ljunggren–Nagell input): the equation `U² + 1 = A⁴B³` has no solution with `U, A, B ≥ 1`. As in the paper this is the single external ingredient, so it is carried as an explicit hypothesis on the main theorems rather than re-proved (it is a deep classical result, not in Mathlib). It is stated as an honest Prop, not assumed via an axiom.
- `coprime_factors_of_sq` (Lemma 2.1): coprime positive integers whose product is a square are each squares.
- `quotient_forced` (Lemma 2.2): for a solution with `x,y ≥ 1`, `z ≥ 0`, `y ∣ x`, and with `d = x/y` one has `z² = d(d²y³ − 1)`, positive when `z > 0`.
- `square_quotient_reduction` (Lemma 2.3): every solution is either `(1,1,0)` or yields `a,u ≥ 1` with `x = a²y`, `z = au`, `u² + 1 = a⁴y³`.
- `only_solution` (Theorem 3.1): assuming the Ljunggren–Nagell input, the only solution of `y(x³ − z²) = x` with `x,y ≥ 1`, `z ≥ 0` is `(1,1,0)`.
- `no_positive_solution` (Corollary 3.2): assuming the input, `y(x³ − z²) = x` has no solution in positive integers.
Appendix A (Gaussian-integer form), in `GaussianInt = ℤ[i]`:
- `gaussAdd`/`gaussAdd_norm`: the element `U + i` and its norm `U² + 1`.
- `prop_A1_parity` (Proposition A.1, parity): if `U² + 1 = A⁴B³` with `U,A,B ≥ 1` then `U` is even and `A`, `B` are odd.
- `prop_A1_coprime` (Proposition A.1, key Gaussian fact): for even `U`, `U + i` and `U − i` are coprime in `ℤ[i]`.
- `prop_A1_norm_converse` (Proposition A.1, easy direction of the equivalence): taking norms in `U + i = ε·α⁴·β³` recovers `U² + 1 = N(α)⁴·N(β)³`.
One part of the appendix is stated but left unproved: the full Gaussian factorisation existence (`U + i = ε·α⁴·β³` with `N(α) = A`, `N(β) = B`). Its proof is the genuine per-prime unique-factorisation grouping in `ℤ[i]` (choosing, for each split prime `ℓ = gₗ·conj gₗ`, the conjugate dividing `U + i`, since an arbitrary Gaussian integer of the right norm fails to be coprime to `U + i`). This is a substantial development not present in Mathlib; rather than leave a `sorry`, its statement and the required argument are recorded in a clearly-labelled comment block, and the provable substance of the appendix is captured by the three proved lemmas above.
The formalization is faithful to the paper: hypotheses match the paper's ranges (`x,y ≥ 1`, `z ≥ 0`, etc.), and the main theorem chain (Lemmas 2.1–2.3 ⟹ Theorem 3.1 ⟹ Corollary 3.2) mirrors the paper exactly, conditional on the stated external input.
