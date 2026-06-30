# Summary of changes for run 70a4776d-9113-43ed-b05f-85082bbda9c5
I formalized, in Lean 4 (Mathlib), the full results of the paper *"Infinitely Many Integer Solutions for Five Related Diophantine Equations"*. Everything lives in `RequestProject/Main.lean`, builds cleanly with no `sorry`, no warnings, and no extra axioms (each main theorem depends only on `propext`, `Classical.choice`, `Quot.sound`).
The five headline theorems each state that the solution set in ℤ³ is infinite (`Set.Infinite`):
- `E1_infinite`: `y² + x³y + z² − 2 = 0`
- `E2_infinite`: `y² + x³y + z² + z − 1 = 0`
- `E3_infinite`: `y² + x³y + z² + z + 1 = 0`
- `E4_infinite`: `y² + x³y + y + z² + 1 = 0`
- `E5_infinite`: `y² + x³y + z² + 1 = 0`
The development follows the paper's constructive structure:
- §1 Descent (Lemma 1.2): `sumsq_descent_nat` and `sumsq_descent_int` deduce, from Fermat's two-squares theorem (`Nat.eq_sq_add_sq_iff`), that if `P²+Q² = m·t²` with `t ≠ 0` then `m` is itself a sum of two integer squares.
- §2 Tangent identity (Lemma 2.1): `tangent_sq_identity` proves `(N⁶+c)·(2(u³+c))²` is a sum of two integer squares whenever `a²+b² = u³+c` and `R² = 4(u³+c)N² − u(u³−8c)`.
- §2′ Pell recurrence (Lemma 2.2): the sequence `pellPair` with lemmas `pellPair_norm`, `pellPair_pos`, `pellPair_N_strictMono`, `pellPair_parity`.
- §3 Core engine: `core_engine` combines the above to produce a strictly increasing sequence of positive integers of fixed parity for which `N⁶+c` is a sum of two integer squares.
- §3′ The four families (Propositions 3.1–3.4): `prop_3_1`…`prop_3_4`, instantiating the engine with the paper's explicit Pell constants (including the large 21- and 35-digit constants of Proposition 3.4, verified by exact integer arithmetic).
- §4 Parity helpers (`even_even_of_sq_add_sq_mod8`, `parity_split_of_sq_add_sq_mod8`) and pointwise conversions (`conv_E1`…`conv_E5`, using the Brahmagupta–Fibonacci identity for E4) turn the two-square values into solutions of the five equations, and a generic projection lemma (`infinite_of_x_infinite`) lifts the infinitude of admissible x-values to infinitude of the full solution set.
The Lean statements faithfully encode the equations and the "infinitely many integer solutions" claim, matching the scope of the paper (existence of an infinite family, not a classification).
