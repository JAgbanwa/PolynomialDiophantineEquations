import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false
/-!
# An infinite family of integer solutions to `z² + y²·z + 2x³ + 1 = 0`
This file formalises the paper *"An Infinite Family of Integer Solutions to
`z² + y²z + 2x³ + 1 = 0`"*.
The strategy is:
* **Lemma 1** (`aux_identity`): a polynomial identity over `ℚ`.
* **Lemma 2** (`conversion`): any factorisation `M² − 2X³ + 1 = 4T⁴` yields a solution
  `(x, y, z) = (−X, 2T, M − 2T²)`.
* **Theorem 1** (`infinite_solutions`): the equation has infinitely many integer solutions,
  via the explicit family of the paper, together with `theorem1_solution`,
  `theorem1_integrality` and `theorem1_distinct` capturing the precise construction.
* **Corollary 1** (`corollary_family`): the explicit polynomial-parametric family.
-/
namespace DiophantineZ2Y2Z
/-- The Diophantine equation under study: `(x, y, z)` is a solution iff
`z² + y²·z + 2x³ + 1 = 0`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + 2 * x ^ 3 + 1 = 0
/-! ## Lemma 1 — the auxiliary identity -/
/-- **Lemma 1.** Let `a` and `n` be rationals with `n = (a² − 1)/2`. Setting
`X = 2n² + a` and `M = 4n³ + 3an + 1` one has
`M² − 2X³ + 1 = (a − 1)⁴ (a + 2)² / 4`. -/
theorem aux_identity (a n : ℚ) (hn : n = (a ^ 2 - 1) / 2) :
    (4 * n ^ 3 + 3 * a * n + 1) ^ 2 - 2 * (2 * n ^ 2 + a) ^ 3 + 1
      = (a - 1) ^ 4 * (a + 2) ^ 2 / 4 := by
  subst hn; ring
/-! ## Lemma 2 — turning a factorisation into a solution -/
/-- **Lemma 2.** If integers `X, M, T` satisfy `M² − 2X³ + 1 = 4T⁴`, then
`(x, y, z) = (−X, 2T, M − 2T²)` is an integer solution of `z² + y²z + 2x³ + 1 = 0`. -/
theorem conversion {X M T : ℤ} (h : M ^ 2 - 2 * X ^ 3 + 1 = 4 * T ^ 4) :
    IsSol (-X) (2 * T) (M - 2 * T ^ 2) := by
  unfold IsSol
  linear_combination h
/-! ## Theorem 1 — the construction -/
/-- The key integer identity behind Theorem 1: with `a = r² − 2`, `2n = a² − 1`,
`2T = r(a − 1)`, `X = 2n² + a` and `M = 4n³ + 3an + 1`, one has `M² − 2X³ + 1 = 4T⁴`.
This is proved by passing to `ℚ`, applying `aux_identity`, and using `a + 2 = r²`. -/
theorem theorem1_key {r a n X T M : ℤ}
    (ha : a = r ^ 2 - 2) (hn : 2 * n = a ^ 2 - 1) (hT : 2 * T = r * (a - 1))
    (hX : X = 2 * n ^ 2 + a) (hM : M = 4 * n ^ 3 + 3 * a * n + 1) :
    M ^ 2 - 2 * X ^ 3 + 1 = 4 * T ^ 4 := by
  have hQ : (M : ℚ) ^ 2 - 2 * (X : ℚ) ^ 3 + 1 = 4 * (T : ℚ) ^ 4 := by
    have hnQ : (n : ℚ) = ((a : ℚ) ^ 2 - 1) / 2 := by
      have : (2 : ℚ) * n = (a : ℚ) ^ 2 - 1 := by exact_mod_cast hn
      linarith
    have hXQ : (X : ℚ) = 2 * (n : ℚ) ^ 2 + a := by exact_mod_cast hX
    have hMQ : (M : ℚ) = 4 * (n : ℚ) ^ 3 + 3 * a * n + 1 := by exact_mod_cast hM
    have haQ : (a : ℚ) = (r : ℚ) ^ 2 - 2 := by exact_mod_cast ha
    have hTQ : (2 : ℚ) * T = (r : ℚ) * ((a : ℚ) - 1) := by exact_mod_cast hT
    rw [hXQ, hMQ, aux_identity (a : ℚ) (n : ℚ) hnQ]
    have ha2 : (a : ℚ) + 2 = (r : ℚ) ^ 2 := by rw [haQ]; ring
    rw [ha2]
    have e : ((r : ℚ) * ((a : ℚ) - 1)) ^ 4 = (2 * (T : ℚ)) ^ 4 := by rw [hTQ]
    linear_combination (1 / 4 : ℚ) * e
  exact_mod_cast hQ
/-- **Theorem 1 (solution part).** With `a = r² − 2`, `2n = a² − 1`, `2T = r(a − 1)`,
`X = 2n² + a` and `M = 4n³ + 3an + 1`, the triple `(−X, 2T, M − 2T²)` is an integer
solution of `z² + y²z + 2x³ + 1 = 0`. -/
theorem theorem1_solution {r a n X T M : ℤ}
    (ha : a = r ^ 2 - 2) (hn : 2 * n = a ^ 2 - 1) (hT : 2 * T = r * (a - 1))
    (hX : X = 2 * n ^ 2 + a) (hM : M = 4 * n ^ 3 + 3 * a * n + 1) :
    IsSol (-X) (2 * T) (M - 2 * T ^ 2) :=
  conversion (theorem1_key ha hn hT hX hM)
/-- **Theorem 1 (integrality part).** For every odd integer `r`, the quantities
`n = (a² − 1)/2` and `T = r(a − 1)/2` (with `a = r² − 2`) are integers. -/
theorem theorem1_integrality {r : ℤ} (hr : Odd r) :
    ∃ n T : ℤ, 2 * n = (r ^ 2 - 2) ^ 2 - 1 ∧ 2 * T = r * ((r ^ 2 - 2) - 1) := by
  obtain ⟨s, rfl⟩ := hr
  exact ⟨8 * s ^ 4 + 16 * s ^ 3 + 4 * s ^ 2 - 4 * s,
    (2 * s + 1) * (2 * s ^ 2 + 2 * s - 1), by ring, by ring⟩
/-! ## The explicit integer family
Writing `r = 2s + 1` makes every quantity of Theorem 1 an explicit integer polynomial
in `s`, which is convenient for proving solution-hood and pairwise distinctness. -/
/-- `a = r² − 2` with `r = 2s + 1`. -/
def aF (s : ℤ) : ℤ := 4 * s ^ 2 + 4 * s - 1
/-- `n = (a² − 1)/2` with `r = 2s + 1`. -/
def nF (s : ℤ) : ℤ := 8 * s ^ 4 + 16 * s ^ 3 + 4 * s ^ 2 - 4 * s
/-- `T = r(a − 1)/2` with `r = 2s + 1`. -/
def TF (s : ℤ) : ℤ := (2 * s + 1) * (2 * s ^ 2 + 2 * s - 1)
/-- `X = 2n² + a`. -/
def XF (s : ℤ) : ℤ := 2 * (nF s) ^ 2 + aF s
/-- `M = 4n³ + 3an + 1`. -/
def MF (s : ℤ) : ℤ := 4 * (nF s) ^ 3 + 3 * (aF s) * (nF s) + 1
/-- The triple `(−X, 2T, M − 2T²)` of the family, as a function of the parameter `s`. -/
def famTriple (s : ℤ) : ℤ × ℤ × ℤ := (-(XF s), 2 * TF s, MF s - 2 * (TF s) ^ 2)
/-- Each member of the explicit family is a genuine integer solution. -/
theorem famTriple_isSol (s : ℤ) :
    IsSol (famTriple s).1 (famTriple s).2.1 (famTriple s).2.2 := by
  unfold IsSol famTriple XF MF TF nF aF
  ring
/-- The map `s ↦ 2T` is strictly increasing on `ℕ`, since `2T = 8s³ + 12s² − 2`. -/
theorem TF_strictMono : StrictMono (fun k : ℕ => 2 * TF (k : ℤ)) := by
  intro i j h
  simp only [TF]
  have hij : (i : ℤ) < (j : ℤ) := by exact_mod_cast h
  have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  nlinarith [hij, hi, mul_nonneg hi hi, mul_pos (sub_pos.mpr hij) (sub_pos.mpr hij)]
/-- The family map `ℕ → ℤ × ℤ × ℤ` is injective: distinct natural parameters give
distinct solutions (this is the "pairwise distinct" claim of Theorem 1). -/
theorem theorem1_distinct : Function.Injective (fun k : ℕ => famTriple (k : ℤ)) := by
  intro i j h
  simp only at h
  apply TF_strictMono.injective
  have h2 : (famTriple (i : ℤ)).2.1 = (famTriple (j : ℤ)).2.1 := by rw [h]
  simpa [famTriple] using h2
/-- **Theorem 1.** The Diophantine equation `z² + y²z + 2x³ + 1 = 0` has infinitely many
integer solutions. -/
theorem infinite_solutions :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Infinite :=
  Set.infinite_of_injective_forall_mem theorem1_distinct (fun k => famTriple_isSol (k : ℤ))
/-! ## Corollary 1 — the polynomial-parametric family
Substituting `a = r² − 2` and simplifying, the solution becomes a polynomial family in `r`.
Over `ℚ` this is a polynomial identity valid for *every* `r`; for odd `r` the coordinates
`xr` and `zr` are integers (their numerators are even). -/
/-- **Corollary 1.** For every `r`, the triple
`xr = −(r⁸ − 8r⁶ + 22r⁴ − 22r² + 5)/2`, `yr = r³ − 3r`,
`zr = (r¹² − 12r¹⁰ + 57r⁸ − 134r⁶ + 159r⁴ − 84r² + 11)/2`
satisfies `zr² + yr²·zr + 2·xr³ + 1 = 0` over `ℚ`. -/
theorem corollary_family (r : ℚ) :
    let xr := -(r ^ 8 - 8 * r ^ 6 + 22 * r ^ 4 - 22 * r ^ 2 + 5) / 2
    let yr := r ^ 3 - 3 * r
    let zr := (r ^ 12 - 12 * r ^ 10 + 57 * r ^ 8 - 134 * r ^ 6 + 159 * r ^ 4
      - 84 * r ^ 2 + 11) / 2
    zr ^ 2 + yr ^ 2 * zr + 2 * xr ^ 3 + 1 = 0 := by
  intro xr yr zr
  simp only [xr, yr, zr]
  ring
/-! ## A worked example
For `r = 3` (i.e. `s = 1`) the construction gives `(x, y, z) = (−1159, 18, 55639)`. -/
example : IsSol (-1159) 18 55639 := by norm_num [IsSol]
example : famTriple 1 = (-1159, 18, 55639) := by
  norm_num [famTriple, XF, MF, TF, nF, aF]
/-! ## Sign symmetry
Since the equation involves `y` only through `y²`, every solution `(x, y, z)` yields the
companion solution `(x, −y, z)`. -/
theorem sign_symmetry {x y z : ℤ} (h : IsSol x y z) : IsSol x (-y) z := by
  unfold IsSol at *
  linear_combination h
end DiophantineZ2Y2Z
