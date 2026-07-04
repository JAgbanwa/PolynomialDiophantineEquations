import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# An Infinite Pellian Family of Integer Solutions to `y² + x²y + z²x + 1 = 0`
This file formalises the note *An Infinite Pellian Family of Integer Solutions to
`y² + x²y + z²x + 1 = 0`*.
The main result (`PellFamily.infinitely_many_solutions`) is that the Diophantine equation
`y² + x²y + z²x + 1 = 0` has infinitely many integer solutions `(x, y, z) ∈ ℤ³`.
The construction fixes `x = -145` (so `x² = 21025`) and reduces the equation to the Pell-type
conic `S² - 580 Z² = 21025² - 4`, where `S = 2y + 21025`.  A single integral point `(39551, 1391)`
on this conic, together with the Pell unit `289 + 12√580` of norm one, generates infinitely many
integral points via the recurrence
`Sₙ₊₁ = 289 Sₙ + 6960 Zₙ`, `Zₙ₊₁ = 12 Sₙ + 289 Zₙ`.
A parity argument then converts all of them back to integer solutions of the original equation.
-/
namespace PellFamily
/-- The pair sequence `(Sₙ, Zₙ)` defined by the recurrence of the paper, with initial value
`(S₀, Z₀) = (39551, 1391)`. -/
def SZ : ℕ → ℤ × ℤ
  | 0 => (39551, 1391)
  | n + 1 => (289 * (SZ n).1 + 6960 * (SZ n).2, 12 * (SZ n).1 + 289 * (SZ n).2)
/-- The `S`-sequence. -/
def Sseq (n : ℕ) : ℤ := (SZ n).1
/-- The `Z`-sequence. -/
def Zseq (n : ℕ) : ℤ := (SZ n).2
@[simp] theorem Sseq_zero : Sseq 0 = 39551 := rfl
@[simp] theorem Zseq_zero : Zseq 0 = 1391 := rfl
theorem Sseq_succ (n : ℕ) : Sseq (n + 1) = 289 * Sseq n + 6960 * Zseq n := rfl
theorem Zseq_succ (n : ℕ) : Zseq (n + 1) = 12 * Sseq n + 289 * Zseq n := rfl
/-
**The Pell unit.** `289² - 580·12² = 1`.
-/
theorem pell_unit : (289 : ℤ) ^ 2 - 580 * 12 ^ 2 = 1 := by
  grind
/-
**Norm preservation (Lemma 3.2).**  The transformation
`(S, Z) ↦ (289 S + 6960 Z, 12 S + 289 Z)` preserves the quadratic form `S² - 580 Z²`.
-/
theorem norm_preserved (S Z : ℤ) :
    (289 * S + 6960 * Z) ^ 2 - 580 * (12 * S + 289 * Z) ^ 2 = S ^ 2 - 580 * Z ^ 2 := by
  grind
/-
**The Pell-type conic identity (Proposition 4.2).**  Every pair `(Sₙ, Zₙ)` lies on the conic
`S² - 580 Z² = 21025² - 4`.
-/
theorem conic (n : ℕ) : Sseq n ^ 2 - 580 * Zseq n ^ 2 = 21025 ^ 2 - 4 := by
  induction' n with n ih;
  · simp only [Sseq_zero, Zseq_zero]; norm_num
  · rw [Sseq_succ, Zseq_succ]; linarith [norm_preserved (Sseq n) (Zseq n)]
/-
Both `Sₙ` and `Zₙ` are strictly positive.
-/
theorem SZ_pos (n : ℕ) : 0 < Sseq n ∧ 0 < Zseq n := by
  induction n <;> simp_all +decide [ Sseq_succ, Zseq_succ ];
  grind
/-
The sequence `Sₙ` is odd for every `n`.
-/
theorem Sseq_odd (n : ℕ) : Odd (Sseq n) := by
  induction' n with n ih;
  · decide +revert;
  · grind +suggestions
/-
The sequence `Sₙ` is strictly increasing.
-/
theorem Sseq_strictMono : StrictMono Sseq := by
  exact strictMono_nat_of_lt_succ fun n => by rw [ Sseq_succ ] ; linarith [ PellFamily.SZ_pos n ] ;
/-- The integer `yₙ = (Sₙ - 21025)/2`. -/
def Yseq (n : ℕ) : ℤ := (Sseq n - 21025) / 2
/-
Because `Sₙ` is odd (and `21025` is odd), `yₙ` genuinely satisfies `2 yₙ = Sₙ - 21025`.
-/
theorem two_mul_Yseq (n : ℕ) : 2 * Yseq n = Sseq n - 21025 := by
  -- Since $S_n$ is odd, $S_n - 21025$ is even, making the division by 2 exact.
  have h_even : Even (Sseq n - 21025) := by
    exact even_iff_two_dvd.mpr ( Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, show Sseq n % 2 = 1 from Int.odd_iff.mp ( Sseq_odd n ) ] ; norm_num ) );
  exact Int.mul_ediv_cancel' ( even_iff_two_dvd.mp h_even )
/-- **The solution triple.** `(xₙ, yₙ, zₙ) = (-145, (Sₙ - 21025)/2, Zₙ)`. -/
def sol (n : ℕ) : ℤ × ℤ × ℤ := (-145, Yseq n, Zseq n)
/-
Each triple `sol n` is an integer solution of the original equation.
-/
theorem sol_mem (n : ℕ) :
    (sol n).2.1 ^ 2 + (sol n).1 ^ 2 * (sol n).2.1 + (sol n).2.2 ^ 2 * (sol n).1 + 1 = 0 := by
  -- By definition of $Yseq$, we have $2 * Yseq n = Sseq n - 21025$.
  have h_Yseq : 2 * Yseq n = Sseq n - 21025 := by
    grind +suggestions;
  -- By definition of $sol$, we have $sol n = (-145, Yseq n, Zseq n)$.
  unfold sol;
  nlinarith [ conic n ]
/-
The `Yseq` sequence is strictly increasing (hence the triples are pairwise distinct).
-/
theorem Yseq_strictMono : StrictMono Yseq := by
  refine' strictMono_nat_of_lt_succ fun n => _;
  exact Int.ediv_lt_of_lt_mul ( by norm_num ) ( by linarith [ Sseq_strictMono n.lt_succ_self, two_mul_Yseq n, two_mul_Yseq ( n + 1 ) ] )
/-
The map `sol` is injective.
-/
theorem sol_injective : Function.Injective sol := by
  intro s t h
  simp [sol] at h
  generalize_proofs at *;
  exact StrictMono.injective Yseq_strictMono h.1
/-- The set of integer solutions of `y² + x²y + z²x + 1 = 0`. -/
def solutionSet : Set (ℤ × ℤ × ℤ) :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 2 * p.2.1 + p.2.2 ^ 2 * p.1 + 1 = 0}
/-- **Theorem 1.1.**  The Diophantine equation `y² + x²y + z²x + 1 = 0` has infinitely many
integer solutions `(x, y, z) ∈ ℤ³`. -/
theorem infinitely_many_solutions : solutionSet.Infinite :=
  Set.infinite_of_injective_forall_mem sol_injective sol_mem
end PellFamily
