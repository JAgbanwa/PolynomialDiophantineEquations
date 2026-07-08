# Summary of changes for run 30c75eed-d95f-4d6e-9fe3-67c05d197f8a
I formalised the paper *Integer Solutions of y² + x²y + xz² − 2 = 0* in Lean 4 (Mathlib), in `RequestProject/Main.lean`, and verified that its central claim — a complete classification of all integer solutions — genuinely holds. The file builds cleanly with no `sorry` and depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
What was formalised (namespace `Diophantine`):
- `IsSol x y z` — the equation `y² + x²·y + x·z² − 2 = 0`.
- The three solution families as predicates: `FamI` (the two exceptional solutions `(1,1,0)`, `(1,−2,0)`), `FamII` (positive-x middle family `(a,−b,±W)` with `0 ≤ b ≤ a²`, `a·W² = b(a²−b)+2`), and `FamIII` (negative-x family, two symmetric branches, with `a·W² = b(b+a²)−2`).
Section 2 preliminaries: `no_sol_x_zero` (Lemma 2.1, no solution with x=0), `involution` (Lemma 2.2), `discriminant_form` (Lemma 2.3).
Sections 3–4: `pos_outer` (Lemma 3.1) and the converse checks `famI_isSol`, `famII_isSol`, `famIII_isSol`.
Section 5 — the main result: `Classification`, an if-and-only-if stating that `IsSol x y z` holds exactly when `(x,y,z)` lies in `FamI`, `FamII`, or `FamIII`. This confirms the paper's Theorem 1.1: the description is both complete (every solution is listed) and sound (every listed triple is a solution), with no other solutions.
Section 6 — the infinite subfamily: the Pell sequence `pell`/`pellU`/`pellZ`, its invariants `pell_props` (positivity, oddness of Uₙ, and Uₙ² − 68·Zₙ² = 83529), monotonicity `pellU_strictMono`, `pell_gives_sol` (Proposition 6.1: each term gives solutions with x = −17), and `sol_infinite`, proving the full integer solution set is infinite.
Conclusion: the paper's claim to describe *all* integer solutions is correct as stated, now machine-checked in Lean. All work is committed and pushed.
