# Summary of changes for run fbcd4ada-abff-45dc-a1f5-c49baa55424c
I formalised the note *An Infinite Pellian Family of Integer Solutions to `y² + x²y + z²x + 1 = 0`* in Lean 4 (Mathlib). All results are proved with no `sorry` and the file builds cleanly; the main theorem depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
The formalization lives in `RequestProject/Main.lean`, in namespace `PellFamily`. It follows the paper's structure:
- `SZ`, `Sseq`, `Zseq`: the integer sequences with `(S₀, Z₀) = (39551, 1391)` and the recurrence `Sₙ₊₁ = 289 Sₙ + 6960 Zₙ`, `Zₙ₊₁ = 12 Sₙ + 289 Zₙ`.
- `pell_unit` (Lemma 3.1): `289² − 580·12² = 1`.
- `norm_preserved` (Lemma 3.2): the map `(S,Z) ↦ (289S+6960Z, 12S+289Z)` preserves `S² − 580 Z²`.
- `conic` (Prop 4.2): every `(Sₙ, Zₙ)` lies on the Pell-type conic `S² − 580 Z² = 21025² − 4`.
- `SZ_pos`, `Sseq_odd`, `Sseq_strictMono`: positivity, oddness of `Sₙ`, and strict monotonicity.
- `Yseq` and `two_mul_Yseq`: the parity argument (Lemma 2.1) showing `yₙ = (Sₙ − 21025)/2` is a genuine integer with `2 yₙ = Sₙ − 21025`.
- `sol`, `sol_mem`, `sol_injective`: the solution triple `(−145, yₙ, Zₙ)` satisfies the original equation, and the map `n ↦` solution is injective.
- `infinitely_many_solutions` (Theorem 1.1): the set `{(x,y,z) ∈ ℤ³ : y² + x²y + z²x + 1 = 0}` is infinite.
This captures the paper's full argument, culminating in the unconditional statement that the Diophantine equation has infinitely many integer solutions.
