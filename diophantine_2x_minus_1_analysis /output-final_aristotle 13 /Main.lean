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
# The Diophantine equation `y * (x ^ 3 - z ^ 2) = 2 * x - 1`

This is the single Lean file of the project: it contains *all* of the results, with no other
source file and no dependency beyond Mathlib.  It is a complete, self-contained analysis of the
integer equation

$$ y\,(x^3 - z^2) \;=\; 2x-1 . $$

The task was to *prove that it has infinitely many integer solutions*.  What is proved below
is everything that the analysis actually supports; the infinitude statement itself is **not**
proved, and the results below explain, rigorously, why: the equation is a disguised
"near-miss between a cube and a square" problem of critical strength, and every natural
source of an infinite family is obstructed by an exact `2`-adic accident.

## The intuition, step by step

**1. The equation is a divisibility statement, and it is extremely rigid.**
Since `2x - 1` is odd, it is never `0`, so `y ≠ 0` and `d := x^3 - z^2 ≠ 0`; moreover `d ∣ 2x-1`
and hence `|d| ≤ |2x-1|` (`abs_sub_le_of_sol`).  For `x ≤ -2` this is impossible because
`|x^3 - z^2| ≥ |x|^3 > 2|x|+1`, so `x ≥ -1` (`neg_one_le_of_sol`).  For large positive `x` it says
that `z^2` lies within `2x-1` of `x^3`.  Consecutive squares near `x^3` are about `2x^{3/2}`
apart, so a random `x` has a chance of only about `x^{-1/2}` of admitting such a `z`; on top of
that the resulting `d` has to be one of the `τ(2x-1)` divisors of `2x-1`.  The expected number of
solutions with `x ≥ X` is therefore of the order of `∑_{x ≥ X} τ(2x-1) x^{-3/2}`, which
*converges*: the heuristic prediction is that the equation has only finitely many solutions.
The numerical picture agrees: the only solutions with `1 ≤ x ≤ 10^7` have `x ∈ {1, 2, 32, 43}`
(`x_mem_of_sol`, verified by a compiled exhaustive search inside Lean), and a separate,
*unverified* search in C finds nothing further up to `x = 10^10`.

**2. Where could an infinite family come from?  Only from an identity.**
For each fixed `y`, `y(x^3-z^2) = 2x-1` is an elliptic curve, hence has finitely many integer
points; the same is true for each fixed `d = x^3-z^2` (a Mordell equation `z^2 = x^3 - d`).
So an infinite family must let both `y` and `d` grow, i.e. it must come from a parametrised
algebraic identity.  A polynomial family `x = X(t)`, `z = Z(t)` needs `deg(X^3 - Z^2) ≤ deg X`,
which by the Davenport–Stothers bound `deg(X^3-Z^2) ≥ deg X / 2 + 1` forces `deg X` even, and
after completing the square every quadratic `X` is `X = S^2 + β`.  Then the truncation
`Z = S^3 + (3β/2) S` is forced, and one gets the *exact* identity (`quadratic_family_identity`)

`(S^2+β)^3 - (S^3 + (3β/2)S)^2 = (β^2/4) · (3(S^2+β) + β)`,

i.e. `x^3 - z^2 = (β²/4)(3x+β)`: along such a family the "defect" is a **linear** function of `x`,
exactly the shape of the right-hand side `2x-1`.  This is why the problem is delicately posed.

**3. The critical family, and the accident that kills it.**
Proportionality of `3x+β` to `2x-1` forces `β = -3/2`, with the ratio `27/32`
(`beta_eq_of_proportional`): for `x = S^2 - 3/2`, `z = S^3 - (9/4)S` one has the identity
`32 (x^3 - z^2) = 27 (2x - 1)` (`critical_family_identity_rat`), whose integral shadow is the
pretty polynomial identity `(u^2-6)^3 - (u^3-9u)^2 = 27(u^2-8)` (`critical_family_identity_int`).
Two things go wrong simultaneously, and both are fatal:
* the proportionality constant is `y = 32/27 ∉ ℤ`, and
* `x = S^2 - 3/2` is never an integer for rational `S` (`critical_family_no_integer_point`):
  `4x + 6 ≡ 2 (mod 4)` is not a square.  The obstruction is `2`-adic, so it cannot be repaired
  by any scaling or twisting of the parameter.

**4. The neighbouring equations do have infinite families — the target one is the exception.**
Taking `β = -2γ` with `γ ∈ ℤ` makes the family integral: `x = u^2 - 2γ`, `z = u^3 - 3γu`, and
`x^3 - z^2 = γ^2 (3x - 2γ)` (`integral_family_identity`).  Hence, for instance,

`y (x^3 - z^2) = 3x - 2` **has infinitely many integer solutions** — take `y = 1`,
`x = u^2 - 2`, `z = u^3 - 3u` (`infinitely_many_sol_three_x_sub_two`),

and similarly for every right-hand side `γ^2(3x-2γ)`.  For the target right-hand side `2x-1`
the same family gives only finitely much: a solution inside it forces
`(3u^2 - 8γ) ∣ (4γ - 3)` (`integral_family_divisibility`), and for `γ = 1` this has no solutions
at all (`no_sol_in_gamma_one_family`).  So the equation `y(x^3-z^2) = 2x-1` sits exactly at the
critical value that all the algebraic families miss.

## What is proved here

* the exhibited solutions `(-1,3,0)`, `(0,1,±1)`, `(1,1,0)`, `(2,-3,±3)`, `(32,9,±181)`,
  `(43,-5,±282)`;
* the structure theorems `y ≠ 0`, `x^3 ≠ z^2`, `(x^3-z^2) ∣ (2x-1)`, `|x^3-z^2| ≤ |2x-1|`,
  `x ≥ -1`, and `x` is never a perfect square `k^2` with `k ≥ 2`;
* the complete determination of the possible `x` with `x ≤ 10^7`: `x ∈ {-1,0,1,2,32,43}`;
* the family identities, the forcing of `β = -3/2`, the impossibility of *any* quadratic family
  with a constant integer `y`, and the `2`-adic obstruction on the critical family;
* the infinitude of the solution set for the sibling equation `y(x^3-z^2) = 3x-2`.

## What is *not* proved

The infinitude of the solution set of `y(x^3-z^2) = 2x-1`.  I could not prove it and believe it
to be out of reach at present (and probably false): it would require infinitely many
`|x^3 - z^2| ≤ 2x-1` *together with* a divisibility condition, while even producing infinitely
many `x` with `|x^3-z^2| ≤ 2x - 1` alone is not something the known Davenport/Danilov-type
constructions give here — the unique family of the right strength is the `2`-adically empty one
of step 3.  Note also that Hall's conjecture, which predicts `|x^3-z^2| ≫ x^{1/2-ε}`, does *not*
decide the question either way.

## Part II: finiteness

The second half of this file (see the section docstring `Part II` below) takes up the opposite
question — whether the equation has only *finitely* many integer solutions.  That direction is
not proved unconditionally either; what is proved is that finiteness is *equivalent* to an upper
bound on `x` (`finitelyManySolutions_iff_bddAbove`), that every bounded range of `x` (and every
fixed `z`) carries only finitely many solutions (`finite_of_x_le`, `finite_of_z_eq`), that above
`x = 3` each `x` carries at most two solutions (`abs_z_eq_of_sol`), that the solutions with
`x ≤ 10^7` are exactly ten explicit triples (`sol_set_le_ten_million`), that the extremal case of
defect `1` (equivalently `y = 2x-1`) has the single solution `(1,1,0)`, by an unconditional
Mordell-type theorem proved from scratch in the Gaussian integers (`cube_sub_sq_eq_one`), and that
no argument based on the *size* of `x^3-z^2` alone can succeed (`infinite_near_misses`).
-/

namespace CubeSquare

/-- The equation under study: `y * (x ^ 3 - z ^ 2) = 2 * x - 1`. -/
def IsSol (x y z : ℤ) : Prop := y * (x ^ 3 - z ^ 2) = 2 * x - 1

/-- The statement that was requested: the solution set of `y(x^3-z^2) = 2x-1` is infinite.

**This is stated, but not proved, here** (and it is not refuted either).  Everything in this file
is evidence about it: see the module docstring.  All solutions found so far have
`x ∈ {-1, 0, 1, 2, 32, 43}`, the search is exhaustive for `x ≤ 10^7` (`x_mem_of_sol`), and the
only algebraic mechanism that could produce an infinite family is obstructed `2`-adically
(`no_constant_y_quadratic_family`, `critical_family_no_integer_point`). -/
def InfinitelyManySolutions : Prop := {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Infinite

/-! ### Explicit solutions -/

theorem sol_neg_one : IsSol (-1) 3 0 := by norm_num [IsSol]
theorem sol_zero_pos : IsSol 0 1 1 := by norm_num [IsSol]
theorem sol_zero_neg : IsSol 0 1 (-1) := by norm_num [IsSol]
theorem sol_one : IsSol 1 1 0 := by norm_num [IsSol]
theorem sol_two : IsSol 2 (-3) 3 := by norm_num [IsSol]
theorem sol_two' : IsSol 2 (-3) (-3) := by norm_num [IsSol]
theorem sol_32 : IsSol 32 9 181 := by norm_num [IsSol]
theorem sol_32' : IsSol 32 9 (-181) := by norm_num [IsSol]
theorem sol_43 : IsSol 43 (-5) 282 := by norm_num [IsSol]
theorem sol_43' : IsSol 43 (-5) (-282) := by norm_num [IsSol]

/-! ### Structure of the solution set -/

theorem sub_ne_zero_of_sol {x y z : ℤ} (h : IsSol x y z) : x ^ 3 - z ^ 2 ≠ 0 := by
  intro h0
  rw [IsSol, h0, mul_zero] at h
  omega

theorem y_ne_zero_of_sol {x y z : ℤ} (h : IsSol x y z) : y ≠ 0 := by
  intro h0
  rw [IsSol, h0, zero_mul] at h
  omega

/-- The defect `x^3 - z^2` divides `2x-1`. -/
theorem dvd_of_sol {x y z : ℤ} (h : IsSol x y z) : (x ^ 3 - z ^ 2) ∣ (2 * x - 1) :=
  ⟨y, by rw [← h]; ring⟩

/-- Hence the defect is *small*: `|x^3 - z^2| ≤ |2x-1|`. -/
theorem abs_sub_le_of_sol {x y z : ℤ} (h : IsSol x y z) : |x ^ 3 - z ^ 2| ≤ |2 * x - 1| := by
  have hpos : 0 < |2 * x - 1| := by
    have : (2 : ℤ) * x - 1 ≠ 0 := by omega
    exact abs_pos.mpr this
  exact Int.le_of_dvd hpos ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr (dvd_of_sol h)))

/-- No solution has `x ≤ -2`: for negative `x` the defect `|x^3 - z^2| ≥ |x|^3` is far too big. -/
theorem neg_one_le_of_sol {x y z : ℤ} (h : IsSol x y z) : -1 ≤ x := by
  by_contra hx
  push Not at hx
  have hx2 : x ≤ -2 := by omega
  have hb := abs_sub_le_of_sol h
  have h1 : |2 * x - 1| = 1 - 2 * x := by rw [abs_of_nonpos] <;> omega
  have hpos : 0 < x ^ 2 - 2 * x + 4 := by nlinarith [sq_nonneg (x - 1)]
  have hcube : x ^ 3 ≤ -8 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr (show x + 2 ≤ 0 by omega)) hpos.le]
  have h2 : |x ^ 3 - z ^ 2| = z ^ 2 - x ^ 3 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg z])]
    ring
  rw [h1, h2] at hb
  have h3 : x - 1 < 0 := by omega
  have h4 : 0 < x ^ 2 + x - 1 := by nlinarith [hx2]
  nlinarith [sq_nonneg z, mul_neg_of_neg_of_pos h3 h4]

/-- **`x` is never a perfect square** (beyond the trivial range): if `x = k^2` with `k ≥ 2` then
`x^3 = (k^3)^2` is itself a square, so the nonzero defect `|x^3-z^2| = |k^3-|z||·(k^3+|z|)` is at
least `k^3 ≥ 2k^2 > 2x-1`.  Thus any solution needs `x^3` to be accidentally close to a square. -/
theorem no_sol_square_x {k y z : ℤ} (hk : 2 ≤ k) : ¬ IsSol (k ^ 2) y z := by
  intro h
  have hne := sub_ne_zero_of_sol h
  have hb := abs_sub_le_of_sol h
  set w := |z| with hw
  have hz2 : z ^ 2 = w ^ 2 := (sq_abs z).symm
  have hw0 : 0 ≤ w := abs_nonneg z
  have hk3 : 8 ≤ k ^ 3 := by nlinarith [hk]
  have hfac : (k ^ 2) ^ 3 - z ^ 2 = (k ^ 3 - w) * (k ^ 3 + w) := by rw [hz2]; ring
  have hne' : k ^ 3 - w ≠ 0 := by
    intro h0
    exact hne (by rw [hfac, h0, zero_mul])
  have h1 : 1 ≤ |k ^ 3 - w| := Int.one_le_abs hne'
  have habs : |(k ^ 2) ^ 3 - z ^ 2| = |k ^ 3 - w| * (k ^ 3 + w) := by
    rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℤ) ≤ k ^ 3 + w)]
  have habs2 : |2 * k ^ 2 - 1| = 2 * k ^ 2 - 1 := abs_of_pos (by nlinarith [hk])
  rw [habs, habs2] at hb
  have hbig : 2 * k ^ 2 ≤ k ^ 3 := by nlinarith [sq_nonneg k, hk]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ |k ^ 3 - w| - 1) (by linarith : (0:ℤ) ≤ k ^ 3 + w)]

/-! ### The quadratic families and the critical parameter

Every polynomial family of "near misses" of the right strength has `x` quadratic in a
parameter; after completing the square, `x = S^2 + β` and `z = S^3 + (3β/2)S`. -/

/-- The basic family identity: the defect of `x = S^2+β`, `z = S^3 + (3β/2)S` is the
*linear* function `(β^2/4)(3x+β)` of `x`. -/
theorem quadratic_family_identity (S β : ℚ) :
    (S ^ 2 + β) ^ 3 - (S ^ 3 + (3 * β / 2) * S) ^ 2
      = β ^ 2 / 4 * (3 * (S ^ 2 + β) + β) := by
  ring

/-- Requiring the defect of such a family to be proportional to the right-hand side `2x-1`
pins the parameter down to `β = -3/2` and the proportionality factor to `27/32`. -/
theorem beta_eq_of_proportional (β k : ℚ) (hk : k ≠ 0)
    (h : ∀ S : ℚ, β ^ 2 / 4 * (3 * (S ^ 2 + β) + β) = k * (2 * (S ^ 2 + β) - 1)) :
    β = -3 / 2 ∧ k = 27 / 32 := by
  have h0 := h 0
  have h1 := h 1
  have hkb : k = 3 * β ^ 2 / 8 := by nlinarith [h0, h1]
  have hβ : β ^ 2 * (2 * β + 3) = 0 := by rw [hkb] at h0; nlinarith [h0]
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb] at hkb
    simp at hkb
    exact hk hkb
  have : 2 * β + 3 = 0 := by
    rcases mul_eq_zero.mp hβ with h' | h'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h') hβ0
    · exact h'
  constructor
  · linarith
  · rw [hkb]; nlinarith [this]

/-- **No quadratic family solves the equation.**  There is no parameter `β ∈ ℚ` and no nonzero
integer `y` for which `x = S^2+β`, `z = S^3 + (3β/2)S` solves the equation identically: the only
candidate parameter is `β = -3/2`, and it needs `y = 32/27 ∉ ℤ`. -/
theorem no_constant_y_quadratic_family (β : ℚ) (y : ℤ) (hy : y ≠ 0)
    (h : ∀ S : ℚ,
      (y : ℚ) * ((S ^ 2 + β) ^ 3 - (S ^ 3 + (3 * β / 2) * S) ^ 2) = 2 * (S ^ 2 + β) - 1) :
    False := by
  have hy' : (y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy
  have hk : ∀ S : ℚ, β ^ 2 / 4 * (3 * (S ^ 2 + β) + β) = (1 / (y : ℚ)) * (2 * (S ^ 2 + β) - 1) := by
    intro S
    rw [← quadratic_family_identity S β, ← h S]
    field_simp
  obtain ⟨-, hk27⟩ := beta_eq_of_proportional β (1 / (y : ℚ)) (one_div_ne_zero hy') hk
  have h32 : (32 : ℚ) = 27 * (y : ℚ) := by
    field_simp at hk27
    linarith
  have : (32 : ℤ) = 27 * y := by exact_mod_cast h32
  omega

/-- The critical family, over `ℚ`: `x = S^2 - 3/2`, `z = S^3 - (9/4)S` satisfies
`32 (x^3 - z^2) = 27 (2x-1)`, i.e. it solves the equation with the *non-integral* value
`y = 32/27`. -/
theorem critical_family_identity_rat (S : ℚ) :
    32 * ((S ^ 2 - 3 / 2) ^ 3 - (S ^ 3 - (9 / 4) * S) ^ 2)
      = 27 * (2 * (S ^ 2 - 3 / 2) - 1) := by
  ring

/-- The integral shadow of the critical identity (clear denominators, `S = u/2`). -/
theorem critical_family_identity_int (u : ℤ) :
    (u ^ 2 - 6) ^ 3 - (u ^ 3 - 9 * u) ^ 2 = 27 * (u ^ 2 - 8) := by
  ring

/-- A rational number whose square is an integer is an integer. -/
theorem isInt_of_sq_isInt {q : ℚ} {n : ℤ} (h : q ^ 2 = (n : ℚ)) : ∃ m : ℤ, q = (m : ℚ) := by
  have hden : (q ^ 2).den = 1 := by rw [h]; simp
  rw [Rat.den_pow] at hden
  have : q.den = 1 := by nlinarith [q.den_pos, hden]
  exact ⟨q.num, by rw [← Rat.num_div_den q, this]; simp⟩

/-- **The `2`-adic obstruction.**  The critical family carries no integer point at all:
`S^2 - 3/2` is never an integer, for any rational `S`. -/
theorem critical_family_no_integer_point (S : ℚ) (x : ℤ) : S ^ 2 - 3 / 2 ≠ (x : ℚ) := by
  intro hS
  have h2 : (2 * S) ^ 2 = ((4 * x + 6 : ℤ) : ℚ) := by push_cast; nlinarith [hS]
  obtain ⟨m, hm⟩ := isInt_of_sq_isInt h2
  rw [hm] at h2
  have : m ^ 2 = 4 * x + 6 := by exact_mod_cast h2
  have hm4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  have hsq : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + m % 4 := ⟨m / 4, by omega⟩
    rcases hm4 with h' | h' | h' | h' <;> rw [hk, h'] <;> [left; right; left; right] <;> ring_nf <;> omega
  omega

/-! ### The integral families: neighbouring equations with infinitely many solutions -/

/-- For every integer `γ`, the pair `x = u^2 - 2γ`, `z = u^3 - 3γu` has defect
`γ^2 (3x - 2γ)`, again a linear function of `x`. -/
theorem integral_family_identity (γ u : ℤ) :
    (u ^ 2 - 2 * γ) ^ 3 - (u ^ 3 - 3 * γ * u) ^ 2
      = γ ^ 2 * (3 * (u ^ 2 - 2 * γ) - 2 * γ) := by
  ring

/-- **A provably infinite sibling.**  `y (x^3 - z^2) = 3x - 2` has infinitely many integer
solutions: `y = 1`, `x = u^2 - 2`, `z = u^3 - 3u`. -/
theorem infinitely_many_sol_three_x_sub_two :
    {p : ℤ × ℤ × ℤ | p.2.1 * (p.1 ^ 3 - p.2.2 ^ 2) = 3 * p.1 - 2}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun u : ℕ => (((u : ℤ) ^ 2 - 2, 1, (u : ℤ) ^ 3 - 3 * (u : ℤ)) : ℤ × ℤ × ℤ)) ?_ ?_
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    have h : (a : ℤ) ^ 2 = (b : ℤ) ^ 2 := by linarith [hab.1]
    have : (a : ℤ) = (b : ℤ) := by
      nlinarith [h, Int.natCast_nonneg a, Int.natCast_nonneg b]
    exact_mod_cast this
  · intro u
    simp only [Set.mem_ofPred_eq]
    ring

/-- Inside the integral family `x = u^2 - 2γ`, `z = u^3 - 3γu` the target equation forces
`3u^2 - 8γ` to divide the constant `4γ - 3`; so each such family contains only finitely many
solutions. -/
theorem integral_family_divisibility {γ u y : ℤ}
    (h : IsSol (u ^ 2 - 2 * γ) y (u ^ 3 - 3 * γ * u)) : (3 * u ^ 2 - 8 * γ) ∣ (4 * γ - 3) := by
  have hd := dvd_of_sol h
  rw [integral_family_identity] at hd
  have hd' : (3 * u ^ 2 - 8 * γ) ∣ (2 * (u ^ 2 - 2 * γ) - 1) := by
    refine dvd_trans ⟨γ ^ 2, by ring⟩ hd
  obtain ⟨c, hc⟩ := hd'
  exact ⟨3 * c - 2, by linarith [hc]⟩

/-- For `γ = 1` the family `x = u^2-2`, `z = u^3-3u` — which solves `y(x^3-z^2) = 3x-2`
identically — contains no solution of `y(x^3-z^2) = 2x-1` whatsoever. -/
theorem no_sol_in_gamma_one_family (u y : ℤ) : ¬ IsSol (u ^ 2 - 2) y (u ^ 3 - 3 * u) := by
  intro h
  have hd := integral_family_divisibility (γ := 1) (by simpa using h)
  norm_num at hd
  have h1 : 3 * u ^ 2 - 8 = 1 ∨ 3 * u ^ 2 - 8 = -1 :=
    Int.isUnit_iff.mp (isUnit_of_dvd_one hd)
  rcases h1 with h' | h'
  · -- `u ^ 2 = 3` is impossible
    have h9 : u ^ 2 = 3 := by linarith
    have hb1 : -2 ≤ u := by nlinarith [h9, sq_nonneg (u + 2)]
    have hb2 : u ≤ 2 := by nlinarith [h9, sq_nonneg (u - 2)]
    interval_cases u <;> simp_all
  · -- `3 u ^ 2 = 7` is impossible
    obtain ⟨v, hv⟩ : ∃ v : ℤ, v = u ^ 2 := ⟨u ^ 2, rfl⟩
    have h7 : 3 * v = 7 := by rw [hv]; linarith
    omega

/-! ### Exhaustive verification for `x ≤ 10^7`

Since `|x^3 - z^2| ≤ 2x-1`, the integer `a = |z|` satisfies
`√(x^3 - (2x-1)) ≤ a ≤ √(x^3 + (2x-1))`, a window containing at most a couple of integers.
The Boolean function below checks, for a given `x = n ≥ 1`, that no `a` in that window yields a
nonzero defect dividing `2x-1`. -/

/-- `noSolAt n = true` certifies that there is no solution with `x = n ≥ 1`. -/
def noSolAt (n : ℕ) : Bool :=
  let lo := Nat.sqrt (n ^ 3 - (2 * n - 1))
  let hi := Nat.sqrt (n ^ 3 + (2 * n - 1))
  (List.range' lo (hi + 1 - lo)).all fun a =>
    (((n : ℤ) ^ 3 - (a : ℤ) ^ 2) == 0) ||
      !(decide (((n : ℤ) ^ 3 - (a : ℤ) ^ 2) ∣ (2 * (n : ℤ) - 1)))

/-- The compiled exhaustive search over `1 ≤ x ≤ 10^7`. -/
theorem searchResult :
    ((List.range' 1 10000000).all fun n =>
      (n == 1) || (n == 2) || (n == 32) || (n == 43) || noSolAt n) = true := by
  native_decide

/-- **Classification of the possible `x` up to `10^7`.**  Every solution with `x ≤ 10^7` has
`x ∈ {-1, 0, 1, 2, 32, 43}` (and all six values do occur). -/
theorem x_mem_of_sol {x y z : ℤ} (h : IsSol x y z) (hub : x ≤ 10000000) :
    x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 32 ∨ x = 43 := by
  have hlb := neg_one_le_of_sol h
  rcases eq_or_lt_of_le hlb with h' | h'
  · exact Or.inl h'.symm
  rcases eq_or_lt_of_le (show (0 : ℤ) ≤ x by omega) with h'' | h''
  · exact Or.inr (Or.inl h''.symm)
  -- now `1 ≤ x`
  have hx1 : 1 ≤ x := h''
  set n : ℕ := x.toNat with hn
  have hxn : (n : ℤ) = x := Int.toNat_of_nonneg (by omega)
  have hn1 : 1 ≤ n := by omega
  have hnub : n < 1 + 10000000 := by omega
  have hmem : n ∈ List.range' 1 10000000 := List.mem_range'_1.mpr ⟨hn1, hnub⟩
  have hall := List.all_eq_true.mp searchResult n hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at hall
  rcases hall with ((((h1 | h2) | h3) | h4) | hns)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  -- the remaining case contradicts the search
  exfalso
  set a : ℕ := z.natAbs with ha
  have haz : (a : ℤ) ^ 2 = z ^ 2 := Int.natAbs_sq z
  have hb := abs_sub_le_of_sol h
  have habs : |2 * x - 1| = 2 * x - 1 := abs_of_pos (by omega)
  rw [habs] at hb
  have hup : x ^ 3 - z ^ 2 ≤ 2 * x - 1 := (abs_le.mp hb).2
  have hlow : -(2 * x - 1) ≤ x ^ 3 - z ^ 2 := (abs_le.mp hb).1
  have h2n : 1 ≤ 2 * n := by omega
  have hcube : 2 * n - 1 ≤ n ^ 3 := by
    have : (2 * (n:ℤ) - 1) ≤ (n:ℤ) ^ 3 := by
      rw [hxn]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by nlinarith [hx1] : (0:ℤ) ≤ x ^ 2 + x - 1)]
    zify [h2n]
    linarith
  have hA : n ^ 3 - (2 * n - 1) ≤ a ^ 2 := by
    have : ((n:ℤ)) ^ 3 - (2 * (n:ℤ) - 1) ≤ (a : ℤ) ^ 2 := by rw [hxn, haz]; linarith
    zify [h2n, hcube]
    linarith
  have hB : a ^ 2 ≤ n ^ 3 + (2 * n - 1) := by
    have : (a : ℤ) ^ 2 ≤ ((n:ℤ)) ^ 3 + (2 * (n:ℤ) - 1) := by rw [hxn, haz]; linarith
    zify [h2n]
    linarith
  have hlo : Nat.sqrt (n ^ 3 - (2 * n - 1)) ≤ a := by
    have := Nat.sqrt_le_sqrt hA
    rwa [Nat.sqrt_eq'] at this
  have hhi : a ≤ Nat.sqrt (n ^ 3 + (2 * n - 1)) := by
    refine Nat.le_sqrt.mpr ?_
    calc a * a = a ^ 2 := by ring
      _ ≤ _ := hB
  simp only [noSolAt] at hns
  have hmem2 : a ∈ List.range'
      (Nat.sqrt (n ^ 3 - (2 * n - 1)))
      (Nat.sqrt (n ^ 3 + (2 * n - 1)) + 1 - Nat.sqrt (n ^ 3 - (2 * n - 1))) :=
    List.mem_range'_1.mpr ⟨hlo, by omega⟩
  have hcheck := List.all_eq_true.mp hns a hmem2
  rw [hxn, haz] at hcheck
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hcheck
  rcases hcheck with hc | hc
  · exact sub_ne_zero_of_sol h hc
  · exact hc (dvd_of_sol h)

/-!
## Part II. Is `y (x^3 - z^2) = 2x - 1` finite?

Everything above analysed the equation from the point of view of *infinitude*.  The second half
of this file examines the opposite question: is the set of integer solutions **finite**?

### The honest verdict, first

I can **not** prove unconditionally that the solution set is finite, and I do not believe such a
proof is available with present-day technology.  The reason is explained precisely below and is
formalised in this file: finiteness is equivalent to an upper bound for the `x`-coordinate
(`finitelyManySolutions_iff_bddAbove`), i.e. to the assertion that for all large `x` no nonzero
`x^3 - z^2` divides `2x-1`.  This is a statement about *near misses between cubes and squares*,
and the size half of it cannot be true for trivial reasons: `infinite_near_misses` proves,
unconditionally, that there are infinitely many `x` carrying a `z` with
`0 < |x^3 - z^2| ≤ 3x`, only a hair above the window `|x^3 - z^2| ≤ 2x-1` that a solution needs.
So any proof of finiteness must exploit the *divisibility* `(x^3-z^2) ∣ (2x-1)`, and the only
unconditional lower bounds known for `|x^3-z^2|` (Baker-type, logarithmic in `x`) are nowhere
near strong enough; even Hall's conjecture, `|x^3-z^2| ≫ x^{1/2-ε}`, is too weak, since it
permits `|x^3-z^2| ≤ 2x-1` infinitely often.  Both the infinitude and the finiteness of the
solution set are therefore open; the heuristic count
`∑_x τ(2x-1)·x^{-3/2} < ∞` of the first half predicts finiteness, and every
numerical experiment agrees, but a prediction is not a proof and this file does not pretend
otherwise.  The statement itself is recorded as `FinitelyManySolutions`, and is left unproved.

### What *is* proved here, unconditionally

1. **Fibre bounds.**  `|x^3 - z^2| ≤ |2x-1|` (`abs_sub_le_of_sol`, above) gives
   `x^3 - |2x-1| ≤ z^2 ≤ x^3 + |2x-1|` (`le_sq_of_sol`, `sq_le_of_sol`), and since the defect is
   a nonzero integer, `|y| ≤ |2x-1|` (`abs_y_le_of_sol`).  So a solution is completely pinned
   down by `x` up to a bounded ambiguity.

2. **Finiteness in every bounded range of `x`** (`finite_of_x_le`): for each `N` the solutions
   with `x ≤ N` form a finite set — they all lie in an explicit box, because `x ≥ -1` bounds `x`
   from below and the fibre bounds then bound `y` and `z`.

3. **The exact reduction** (`finitelyManySolutions_iff_bddAbove`): the equation has finitely many
   solutions **iff** the `x`-coordinates of the solutions are bounded above; and
   (`finitelyManySolutions_of_eventually_not_dvd`) it suffices that, for all large `x`, no nonzero
   `x^3 - z^2` divides `2x-1`.  This eliminates `y` and reduces a three-variable problem to a
   one-variable divisibility question.

4. **The `z`-fibres are finite too** (`x_le_abs_z_of_sol`, `finite_of_z_eq`): a solution with
   `x ≥ 2` satisfies `x ≤ |z|`, because otherwise `x^3 - z^2 > 2x-1` outright.  Hence for each
   fixed `z` there are only finitely many solutions, and boundedness of `z` would also suffice
   for finiteness.  (By contrast, finiteness of the fibre over a fixed `y` is a statement about
   integral points on an elliptic curve — true by Siegel's theorem, but not something the present
   development contains, and useless here anyway since `y` is unbounded along the fibres of `x`.)

5. **At most two solutions over each `x ≥ 4`** (`abs_z_eq_of_sol`): the window
   `x^3 - (2x-1) ≤ z^2 ≤ x^3 + (2x-1)` has width `4x-2`, whereas consecutive squares near `x^3`
   differ by about `2x^{3/2}`; so at most one value of `|z|` can occur, and `y` is then
   determined.  The solution set is therefore in two-to-one correspondence with its set of
   `x`-values (above `x = 3`).

6. **A complete, unconditional finiteness theorem in the searched range**
   (`sol_set_le_ten_million`, `finite_sol_set_le_ten_million`): the solutions with `x ≤ 10^7` are
   *exactly* the ten triples
   `(-1,3,0)`, `(0,1,±1)`, `(1,1,0)`, `(2,-3,±3)`, `(32,9,±181)`, `(43,-5,±282)`.
   This upgrades the `x`-classification of `x_mem_of_sol` to a complete determination
   of `y` and `z` as well, using the narrow-window argument of item 5.

7. **The extremal case, unconditionally** (`cube_sub_sq_eq_one`, `sol_of_defect_one`,
   `sol_set_defect_one`): the solutions whose defect is exactly `1` — equivalently those with the
   largest possible multiplier `y = 2x-1` — reduce to the Mordell equation `z^2 + 1 = x^3`, which
   is solved here from scratch by factoring `z+i` in the Gaussian integers.  The only solution is
   `(x,y,z) = (1,1,0)`.  (The mirror case of defect `-1`, which is where the solutions
   `(-1,3,0)`, `(0,1,±1)` and `(2,-3,±3)` live, leads to the Thue equation `s^3 - 2t^3 = ±1` and
   is not treated here.)

8. **Why the size condition alone cannot decide it** (`infinite_near_misses`): the integral family
   `x = u^2-2`, `z = u^3-3u` has `x^3 - z^2 = 3x-2`, so near misses of *linear* size in `x` occur
   infinitely often.  The whole difficulty of the problem lives in the factor `3` versus `2`: for
   the right-hand side `3x-2` the family solves the equation identically with `y = 1`
   (`infinitely_many_sol_three_x_sub_two`), whereas for `2x-1` the same families give
   nothing (`no_sol_in_gamma_one_family`).

In summary: the finiteness of the solution set is *equivalent*, by the results below, to a clean
one-variable statement, it is supported by an exhaustive verification up to `x = 10^7` and by a
convergent heuristic count, and it is out of reach of current unconditional methods, exactly as
the infinitude claim of the first half is.
-/


/-- The statement that the solution set of `y(x^3-z^2) = 2x-1` is finite. -/
def FinitelyManySolutions : Prop := {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Finite

/-! ### Fibre bounds -/

theorem sq_le_of_sol {x y z : ℤ} (h : IsSol x y z) : z ^ 2 ≤ x ^ 3 + |2 * x - 1| := by
  have := neg_le_of_abs_le (abs_sub_le_of_sol h)
  linarith

theorem le_sq_of_sol {x y z : ℤ} (h : IsSol x y z) : x ^ 3 - |2 * x - 1| ≤ z ^ 2 := by
  have := le_of_abs_le (abs_sub_le_of_sol h)
  linarith

/-- The multiplier `y` is bounded by the right-hand side: `|y| ≤ |2x-1|`. -/
theorem abs_y_le_of_sol {x y z : ℤ} (h : IsSol x y z) : |y| ≤ |2 * x - 1| := by
  have h1 : 1 ≤ |x ^ 3 - z ^ 2| := Int.one_le_abs (sub_ne_zero_of_sol h)
  have h2 : |y| * |x ^ 3 - z ^ 2| = |2 * x - 1| := by rw [← abs_mul, h]
  nlinarith [abs_nonneg y]

/-- `|z| ≤ z ^ 2` for integers. -/
private theorem abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  rcases eq_or_lt_of_le (abs_nonneg z) with h | h
  · nlinarith [sq_abs z]
  · have : 1 ≤ |z| := h
    nlinarith [sq_abs z]

/-! ### Finiteness in any bounded range of `x` -/

/-- **Unconditional finiteness in bounded ranges.** For every `N` there are only finitely many
solutions with `x ≤ N`: the constraint `x ≥ -1` bounds `x` from below, `|x^3 - z^2| ≤ |2x-1|`
bounds `z`, and `|y| ≤ |2x-1|` bounds `y`. -/
theorem finite_of_x_le (N : ℤ) :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2 ∧ p.1 ≤ N}.Finite := by
  set B : ℤ := |N| ^ 3 + 2 * |N| + 4 with hBdef
  have hN0 : 0 ≤ |N| := abs_nonneg N
  have hcube3 : 0 ≤ |N| ^ 3 := pow_nonneg hN0 3
  have hB4 : 4 ≤ B := by rw [hBdef]; linarith
  have hBge : |N| ≤ B := by rw [hBdef]; linarith
  have hBge' : 2 * |N| + 3 ≤ B := by rw [hBdef]; linarith
  refine Set.Finite.subset
    ((Set.finite_Icc (-B) B).prod ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B))) ?_
  rintro ⟨x, y, z⟩ ⟨hsol, hxN⟩
  have hx1 : -1 ≤ x := neg_one_le_of_sol hsol
  have hxa : x ≤ |N| := le_trans hxN (le_abs_self N)
  -- the right-hand side is small
  have hrhs : |2 * x - 1| ≤ 2 * |N| + 3 := by
    rw [abs_le]; constructor <;> linarith
  -- bound on `x`
  have hxB : -B ≤ x ∧ x ≤ B := by constructor <;> linarith
  -- bound on `y`
  have hyB : -B ≤ y ∧ y ≤ B := by
    have := abs_y_le_of_sol hsol
    have h' : |y| ≤ B := by linarith
    exact abs_le.mp h'
  -- bound on `z`
  have hzB : -B ≤ z ∧ z ≤ B := by
    have hcube : x ^ 3 ≤ |N| ^ 3 := by nlinarith [sq_nonneg (x + |N|), sq_nonneg x, sq_nonneg |N|]
    have hz2 : z ^ 2 ≤ B := by
      have := sq_le_of_sol hsol
      linarith
    have : |z| ≤ B := le_trans (abs_le_sq z) hz2
    exact abs_le.mp this
  exact ⟨Set.mem_Icc.mpr hxB, Set.mem_Icc.mpr hyB, Set.mem_Icc.mpr hzB⟩

/-- **Reduction.** The equation has finitely many solutions if and only if the `x`-coordinates
of its solutions are bounded above. -/
theorem finitelyManySolutions_iff_bddAbove :
    FinitelyManySolutions ↔ ∃ N : ℤ, ∀ x y z : ℤ, IsSol x y z → x ≤ N := by
  constructor
  · intro hfin
    obtain ⟨N, hN⟩ := (hfin.image (fun p : ℤ × ℤ × ℤ => p.1)).bddAbove
    exact ⟨N, fun x y z h => hN ⟨(x, y, z), h, rfl⟩⟩
  · rintro ⟨N, hN⟩
    refine Set.Finite.subset (finite_of_x_le N) ?_
    rintro ⟨x, y, z⟩ h
    exact ⟨h, hN x y z h⟩

/-- **A sufficient criterion**, with `y` and `z` eliminated: if for all large `x` no nonzero
defect `x^3 - z^2` divides `2x-1`, the equation has finitely many solutions. -/
theorem finitelyManySolutions_of_eventually_not_dvd
    (h : ∃ N : ℤ, ∀ x z : ℤ, N < x → x ^ 3 - z ^ 2 ≠ 0 → ¬ ((x ^ 3 - z ^ 2) ∣ (2 * x - 1))) :
    FinitelyManySolutions := by
  obtain ⟨N, hN⟩ := h
  refine finitelyManySolutions_iff_bddAbove.mpr ⟨N, fun x y z hsol => ?_⟩
  by_contra hx
  exact hN x z (lt_of_not_ge hx) (sub_ne_zero_of_sol hsol) (dvd_of_sol hsol)

/-! ### The fibres over a fixed `z` -/

/-- A solution with `x ≥ 2` has `x ≤ |z|`: otherwise `z ^ 2 ≤ (x-1) ^ 2` and the defect
`x^3 - z^2 ≥ x^3 - x^2 + 2x - 1` already exceeds `2x-1`. -/
theorem x_le_abs_z_of_sol {x y z : ℤ} (h : IsSol x y z) (hx : 2 ≤ x) : x ≤ |z| := by
  by_contra hc
  push Not at hc
  have h1 : |z| ≤ x - 1 := by omega
  have h2 : z ^ 2 ≤ (x - 1) ^ 2 := by
    rw [← sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg z) h1 2
  have h3 := le_sq_of_sol h
  rw [abs_of_pos (by omega : (0:ℤ) < 2 * x - 1)] at h3
  nlinarith

/-- **The fibre over each fixed `z` is finite.** -/
theorem finite_of_z_eq (z₀ : ℤ) :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2 ∧ p.2.2 = z₀}.Finite := by
  refine Set.Finite.subset (finite_of_x_le (max |z₀| 1)) ?_
  rintro ⟨x, y, z⟩ ⟨hsol, hz⟩
  refine ⟨hsol, ?_⟩
  rcases lt_or_ge x 2 with hx | hx
  · exact le_trans (show x ≤ 1 by omega) (le_max_right |z₀| 1)
  · exact le_trans (by rw [← hz]; exact x_le_abs_z_of_sol hsol hx) (le_max_left |z₀| 1)

/-! ### At most two solutions above each `x ≥ 4` -/

/-- For `x ≥ 4` the window `x^3 - (2x-1) ≤ z^2 ≤ x^3 + (2x-1)` is too narrow to contain two
distinct squares: any two solutions with the same `x` have the same `|z|`. -/
theorem abs_z_eq_of_sol {x y z y' z' : ℤ} (hx : 4 ≤ x) (h : IsSol x y z) (h' : IsSol x y' z') :
    |z| = |z'| := by
  have habs : |2 * x - 1| = 2 * x - 1 := abs_of_pos (by omega)
  have b1 := sq_le_of_sol h
  have b2 := le_sq_of_sol h
  have b3 := sq_le_of_sol h'
  have b4 := le_sq_of_sol h'
  rw [habs] at b1 b2 b3 b4
  -- both `|z|` and `|z'|` are at least `2x-1`
  have key : ∀ w : ℤ, x ^ 3 - (2 * x - 1) ≤ w ^ 2 → 2 * x - 1 ≤ |w| := by
    intro w hw
    by_contra hc
    push Not at hc
    have h0 : 0 ≤ |w| := abs_nonneg w
    nlinarith [sq_abs w, sq_nonneg (x - 4), sq_nonneg x]
  have hz := key z b2
  have hz' := key z' b4
  have hzz : |z| ^ 2 = z ^ 2 := sq_abs z
  have hzz' : |z'| ^ 2 = z' ^ 2 := sq_abs z'
  rcases lt_trichotomy |z| |z'| with hlt | heq | hgt
  · exfalso; nlinarith
  · exact heq
  · exfalso; nlinarith

/-! ### The size condition alone cannot give finiteness -/

/-- **Why the size estimate is not enough.** There are infinitely many `x` admitting a `z` with
`0 < |x^3 - z^2| ≤ 3x`, namely `x = u^2 - 2`, `z = u^3 - 3u`, for which `x^3 - z^2 = 3x-2`.
So a Hall-type lower bound on `|x^3 - z^2|` of the shape `≫ x` is *false*: any proof of
finiteness must use the divisibility `(x^3-z^2) ∣ (2x-1)`, not just its size consequence. -/
theorem infinite_near_misses :
    {x : ℤ | ∃ z : ℤ, 0 < |x ^ 3 - z ^ 2| ∧ |x ^ 3 - z ^ 2| ≤ 3 * x}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun u : ℕ => ((u : ℤ) + 2) ^ 2 - 2) ?_ ?_
  · intro a b hab
    simp only at hab
    have h : ((a : ℤ) + 2) ^ 2 = ((b : ℤ) + 2) ^ 2 := by linarith
    have : (a : ℤ) = (b : ℤ) := by
      nlinarith [Int.natCast_nonneg a, Int.natCast_nonneg b]
    exact_mod_cast this
  · intro u
    have hu : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
    refine ⟨((u : ℤ) + 2) ^ 3 - 3 * ((u : ℤ) + 2), ?_, ?_⟩
    · rw [show (((u : ℤ) + 2) ^ 2 - 2) ^ 3 - (((u : ℤ) + 2) ^ 3 - 3 * ((u : ℤ) + 2)) ^ 2
        = 3 * (((u : ℤ) + 2) ^ 2 - 2) - 2 by ring]
      rw [abs_of_pos (by nlinarith)]
      nlinarith
    · rw [show (((u : ℤ) + 2) ^ 2 - 2) ^ 3 - (((u : ℤ) + 2) ^ 3 - 3 * ((u : ℤ) + 2)) ^ 2
        = 3 * (((u : ℤ) + 2) ^ 2 - 2) - 2 by ring]
      rw [abs_of_pos (by nlinarith)]
      nlinarith

/-! ### The complete solution set for `x ≤ 10^7` -/

/-- If `z ^ 2` lies strictly between `(a-1) ^ 2` and `(a+1) ^ 2` then `z = ± a`. -/
private theorem z_eq_window {z a : ℤ} (ha : 1 ≤ a) (h1 : (a - 1) ^ 2 < z ^ 2)
    (h2 : z ^ 2 < (a + 1) ^ 2) : z = a ∨ z = -a := by
  have u1 : |a - 1| < |z| := sq_lt_sq.mp h1
  have u2 : |z| < |a + 1| := sq_lt_sq.mp h2
  rw [abs_of_nonneg (by omega : (0:ℤ) ≤ a - 1)] at u1
  rw [abs_of_nonneg (by omega : (0:ℤ) ≤ a + 1)] at u2
  have h3 : |z| = a := by omega
  rcases (abs_eq (by omega : (0:ℤ) ≤ a)).mp h3 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem sol_x_neg_one {y z : ℤ} (h : IsSol (-1) y z) : y = 3 ∧ z = 0 := by
  have hs := sq_le_of_sol h
  have e : ((-1 : ℤ)) ^ 3 + |2 * (-1 : ℤ) - 1| = 2 := by norm_num
  have h1 : z ^ 2 ≤ 2 := by linarith
  have hb1 : -1 ≤ z := by nlinarith
  have hb2 : z ≤ 1 := by nlinarith
  unfold IsSol at h
  interval_cases z <;> norm_num at h <;> omega

theorem sol_x_zero {y z : ℤ} (h : IsSol 0 y z) : y = 1 ∧ (z = 1 ∨ z = -1) := by
  have hs := sq_le_of_sol h
  have e : ((0 : ℤ)) ^ 3 + |2 * (0 : ℤ) - 1| = 1 := by norm_num
  have h1 : z ^ 2 ≤ 1 := by linarith
  have hb1 : -1 ≤ z := by nlinarith
  have hb2 : z ≤ 1 := by nlinarith
  unfold IsSol at h
  interval_cases z <;> norm_num at h <;> omega

theorem sol_x_one {y z : ℤ} (h : IsSol 1 y z) : y = 1 ∧ z = 0 := by
  have hs := sq_le_of_sol h
  have e : ((1 : ℤ)) ^ 3 + |2 * (1 : ℤ) - 1| = 2 := by norm_num
  have h1 : z ^ 2 ≤ 2 := by linarith
  have hb1 : -1 ≤ z := by nlinarith
  have hb2 : z ≤ 1 := by nlinarith
  unfold IsSol at h
  interval_cases z
  all_goals norm_num at h
  all_goals omega

theorem sol_x_two {y z : ℤ} (h : IsSol 2 y z) : y = -3 ∧ (z = 3 ∨ z = -3) := by
  have hs := sq_le_of_sol h
  have hs' := le_sq_of_sol h
  have e : ((2 : ℤ)) ^ 3 + |2 * (2 : ℤ) - 1| = 11 := by norm_num
  have e' : ((2 : ℤ)) ^ 3 - |2 * (2 : ℤ) - 1| = 5 := by norm_num
  have h1 : z ^ 2 ≤ 11 := by linarith
  have h2 : 5 ≤ z ^ 2 := by linarith
  have hz : z = 3 ∨ z = -3 :=
    z_eq_window (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨?_, hz⟩
  unfold IsSol at h
  rcases hz with rfl | rfl <;> norm_num at h <;> omega

theorem sol_x_32 {y z : ℤ} (h : IsSol 32 y z) : y = 9 ∧ (z = 181 ∨ z = -181) := by
  have hs := sq_le_of_sol h
  have hs' := le_sq_of_sol h
  have e : ((32 : ℤ)) ^ 3 + |2 * (32 : ℤ) - 1| = 32831 := by norm_num
  have e' : ((32 : ℤ)) ^ 3 - |2 * (32 : ℤ) - 1| = 32705 := by norm_num
  have h1 : z ^ 2 ≤ 32831 := by linarith
  have h2 : 32705 ≤ z ^ 2 := by linarith
  have hz : z = 181 ∨ z = -181 :=
    z_eq_window (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨?_, hz⟩
  unfold IsSol at h
  rcases hz with rfl | rfl <;> norm_num at h <;> omega

theorem sol_x_43 {y z : ℤ} (h : IsSol 43 y z) : y = -5 ∧ (z = 282 ∨ z = -282) := by
  have hs := sq_le_of_sol h
  have hs' := le_sq_of_sol h
  have e : ((43 : ℤ)) ^ 3 + |2 * (43 : ℤ) - 1| = 79592 := by norm_num
  have e' : ((43 : ℤ)) ^ 3 - |2 * (43 : ℤ) - 1| = 79422 := by norm_num
  have h1 : z ^ 2 ≤ 79592 := by linarith
  have h2 : 79422 ≤ z ^ 2 := by linarith
  have hz : z = 282 ∨ z = -282 :=
    z_eq_window (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨?_, hz⟩
  unfold IsSol at h
  rcases hz with rfl | rfl <;> norm_num at h <;> omega

/-- **The complete list of solutions with `x ≤ 10^7`.** -/
theorem sol_set_le_ten_million :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2 ∧ p.1 ≤ 10 ^ 7} =
      {(-1, 3, 0), (0, 1, 1), (0, 1, -1), (1, 1, 0), (2, -3, 3), (2, -3, -3),
       (32, 9, 181), (32, 9, -181), (43, -5, 282), (43, -5, -282)} := by
  ext ⟨x, y, z⟩
  constructor
  · rintro ⟨hsol, hub⟩
    have hub' : x ≤ 10000000 := by norm_num at hub; exact hub
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    rcases x_mem_of_sol hsol hub' with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨rfl, rfl⟩ := sol_x_neg_one hsol; norm_num
    · obtain ⟨rfl, hz⟩ := sol_x_zero hsol; rcases hz with rfl | rfl <;> norm_num
    · obtain ⟨rfl, rfl⟩ := sol_x_one hsol; norm_num
    · obtain ⟨rfl, hz⟩ := sol_x_two hsol; rcases hz with rfl | rfl <;> norm_num
    · obtain ⟨rfl, hz⟩ := sol_x_32 hsol; rcases hz with rfl | rfl <;> norm_num
    · obtain ⟨rfl, hz⟩ := sol_x_43 hsol; rcases hz with rfl | rfl <;> norm_num
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact ⟨by norm_num [IsSol], by norm_num⟩

/-- **Unconditional finiteness up to `10^7`**: exactly ten solutions have `x ≤ 10^7`. -/
theorem finite_sol_set_le_ten_million :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2 ∧ p.1 ≤ 10 ^ 7}.Finite := by
  rw [sol_set_le_ten_million]
  exact Set.toFinite _

/-! ### The unit-defect case: an unconditional Mordell theorem

The case `|y|` maximal, i.e. defect `x^3 - z^2 = 1`, is exactly the Mordell equation
`z^2 + 1 = x^3`.  Here finiteness *can* be proved unconditionally, by factoring in the Gaussian
integers `ℤ[i]`: `z` must be even, so `z+i` and `z-i` are coprime in `ℤ[i]`; their product is a
cube, hence each is a cube times a unit, and every unit of `ℤ[i]` is itself a cube (the unit group
has order `4`, coprime to `3`).  Writing `z + i = (a+bi)^3` and comparing imaginary parts gives
`b(3a^2-b^2) = 1`, whence `b = -1`, `a = 0`, `z = 0` and `x = 1`. -/

section Mordell

open Zsqrtd

noncomputable local instance : GCDMonoid GaussianInt := UniqueFactorizationMonoid.toGCDMonoid _

private theorem gi_norm (a b : ℤ) : (⟨a, b⟩ : GaussianInt).norm = a ^ 2 + b ^ 2 := by
  simp [Zsqrtd.norm]; ring

private theorem gi_cube (a b : ℤ) :
    (⟨a, b⟩ : GaussianInt) ^ 3 = ⟨a ^ 3 - 3 * a * b ^ 2, 3 * a ^ 2 * b - b ^ 3⟩ := by
  ext <;> simp [pow_succ] <;> ring

private theorem gi_norm_dvd {a b : GaussianInt} (h : a ∣ b) : a.norm ∣ b.norm := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.norm, by rw [Zsqrtd.norm_mul]⟩

/-- Every unit of `ℤ[i]` is a cube: the unit group `{±1, ±i}` has order `4`, coprime to `3`. -/
private theorem gi_unit_cube {u : GaussianInt} (hu : IsUnit u) : ∃ v : GaussianInt, u = v ^ 3 := by
  obtain ⟨a, b⟩ := u
  have h := Zsqrtd.norm_eq_one_iff.mpr hu
  rw [gi_norm] at h
  have h1 : a ^ 2 + b ^ 2 = 1 := by
    rcases Int.natAbs_eq_iff.mp h with h' | h'
    · exact_mod_cast h'
    · push_cast at h'
      nlinarith [sq_nonneg a, sq_nonneg b]
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg a]
  clear h hu
  interval_cases a <;> interval_cases b <;> revert h1 <;> norm_num <;>
    first
      | exact ⟨⟨1, 0⟩, by decide⟩
      | exact ⟨⟨-1, 0⟩, by decide⟩
      | exact ⟨⟨0, 1⟩, by decide⟩
      | exact ⟨⟨0, -1⟩, by decide⟩

/-- If `z ^ 2 + 1 = x ^ 3` then `z = 0`: a cube exceeds a square by `1` only in the trivial way.
(This is the classical Mordell equation `z^2 = x^3 - 1`, proved here from scratch in `ℤ[i]`.) -/
theorem cube_sub_sq_eq_one {x z : ℤ} (h : x ^ 3 - z ^ 2 = 1) : x = 1 ∧ z = 0 := by
  -- `z` is even, since otherwise `x^3 = z^2+1` has `2`-adic valuation exactly `1`
  obtain ⟨k, hk⟩ : ∃ k, z = 2 * k := by
    rcases Int.even_or_odd z with he | ho
    · obtain ⟨k, hk⟩ := he; exact ⟨k, by omega⟩
    · exfalso
      obtain ⟨k, hk⟩ := ho
      have hx3 : x ^ 3 = 4 * k ^ 2 + 4 * k + 2 := by rw [hk] at h; nlinarith [h]
      have hxe : Even x := by
        rcases Int.even_or_odd x with he | ⟨m, hm⟩
        · exact he
        · exfalso
          have hx : x ^ 3 = 8 * m ^ 3 + 12 * m ^ 2 + 6 * m + 1 := by rw [hm]; ring
          obtain ⟨M, hM⟩ : ∃ M : ℤ, M = m ^ 3 := ⟨_, rfl⟩
          obtain ⟨K, hK⟩ : ∃ K : ℤ, K = m ^ 2 := ⟨_, rfl⟩
          obtain ⟨L, hL⟩ : ∃ L : ℤ, L = k ^ 2 := ⟨_, rfl⟩
          rw [← hM, ← hK] at hx
          rw [← hL] at hx3
          omega
      obtain ⟨m, hm⟩ := hxe
      have h8 : 8 * m ^ 3 = 4 * k ^ 2 + 4 * k + 2 := by rw [hm] at hx3; nlinarith [hx3]
      obtain ⟨M, hM⟩ : ∃ M : ℤ, M = m ^ 3 := ⟨_, rfl⟩
      obtain ⟨L, hL⟩ : ∃ L : ℤ, L = k ^ 2 := ⟨_, rfl⟩
      rw [← hM, ← hL] at h8
      omega
  -- factor `z^2 + 1 = (z+i)(z-i) = x^3` in `ℤ[i]`
  have hmul : (⟨z, 1⟩ : GaussianInt) * ⟨z, -1⟩ = (⟨x, 0⟩ : GaussianInt) ^ 3 := by
    rw [gi_cube]
    ext
    · simp; nlinarith [h]
    · simp
  -- `z+i` and `z-i` are coprime, because their difference `2i` has even norm and `z^2+1` is odd
  have hcop : IsUnit (gcd (⟨z, 1⟩ : GaussianInt) ⟨z, -1⟩) := by
    have hg1 : gcd (⟨z, 1⟩ : GaussianInt) ⟨z, -1⟩ ∣ (⟨z, 1⟩ : GaussianInt) := gcd_dvd_left _ _
    have hg2 : gcd (⟨z, 1⟩ : GaussianInt) ⟨z, -1⟩ ∣ (⟨z, -1⟩ : GaussianInt) := gcd_dvd_right _ _
    have hsub : (⟨z, 1⟩ : GaussianInt) - ⟨z, -1⟩ = ⟨0, 2⟩ := by ext <;> simp
    have hgd : gcd (⟨z, 1⟩ : GaussianInt) ⟨z, -1⟩ ∣ (⟨0, 2⟩ : GaussianInt) := by
      rw [← hsub]; exact dvd_sub hg1 hg2
    have hn1 := gi_norm_dvd hg1
    have hn2 := gi_norm_dvd hgd
    rw [gi_norm z 1] at hn1
    rw [gi_norm 0 2] at hn2
    set g := gcd (⟨z, 1⟩ : GaussianInt) ⟨z, -1⟩ with hgdef
    have h4 : g.norm ∣ (4 : ℤ) := by simpa using hn2
    have hodd : ¬ (2 : ℤ) ∣ z ^ 2 + 1 ^ 2 := by
      rintro ⟨c, hc⟩
      obtain ⟨K, hK⟩ : ∃ K : ℤ, K = k ^ 2 := ⟨_, rfl⟩
      rw [hk] at hc
      have : 4 * K + 1 = 2 * c := by rw [hK]; linarith [hc]
      omega
    have hne : ¬ (2 : ℤ) ∣ g.norm := fun hd => hodd (dvd_trans hd hn1)
    have hm : g.norm.natAbs ∣ 4 := by
      have := Int.natAbs_dvd_natAbs.mpr h4
      simpa using this
    have hle : g.norm.natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) hm
    have h1 : g.norm.natAbs = 1 := by
      interval_cases hcase : g.norm.natAbs
      · simp at hm
      · rfl
      · exact absurd (by rcases Int.natAbs_eq_iff.mp hcase with h' | h' <;> omega) hne
      · norm_num at hm
      · exact absurd (by rcases Int.natAbs_eq_iff.mp hcase with h' | h' <;> omega) hne
    exact Zsqrtd.norm_eq_one_iff.mp h1
  -- so `z + i` is a cube in `ℤ[i]`
  obtain ⟨β, u, hu⟩ := exists_associated_pow_of_mul_eq_pow hcop hmul
  obtain ⟨v, hv⟩ := gi_unit_cube u.isUnit
  have hcube : (β * v) ^ 3 = (⟨z, 1⟩ : GaussianInt) := by rw [mul_pow, ← hv, hu]
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, β * v = ⟨a, b⟩ := ⟨(β * v).re, (β * v).im, rfl⟩
  rw [hab, gi_cube] at hcube
  have h1 : a ^ 3 - 3 * a * b ^ 2 = z := congrArg Zsqrtd.re hcube
  have h2 : 3 * a ^ 2 * b - b ^ 3 = 1 := congrArg Zsqrtd.im hcube
  -- comparing imaginary parts: `b (3a^2 - b^2) = 1`
  have hb : b ∣ 1 := ⟨3 * a ^ 2 - b ^ 2, by linarith [h2,
    (by ring : b * (3 * a ^ 2 - b ^ 2) = 3 * a ^ 2 * b - b ^ 3)]⟩
  have hz : z = 0 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hb) with rfl | rfl
    · exfalso
      obtain ⟨A, hA⟩ : ∃ A : ℤ, A = a ^ 2 := ⟨_, rfl⟩
      rw [← hA] at h2
      omega
    · have ha : a = 0 := by nlinarith [h2, sq_nonneg a]
      rw [← h1, ha]; ring
  refine ⟨?_, hz⟩
  rw [hz] at h
  nlinarith [h, sq_nonneg (x - 1), sq_nonneg (x + 1)]

/-- **The extremal case is unconditionally finite.**  A solution whose defect is `1` — equivalently
one with `y = 2x-1`, the largest possible multiplier — must be `(x,y,z) = (1,1,0)`. -/
theorem sol_of_defect_one {x y z : ℤ} (h : IsSol x y z) (hd : x ^ 3 - z ^ 2 = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 := by
  obtain ⟨hx, hz⟩ := cube_sub_sq_eq_one hd
  refine ⟨hx, ?_, hz⟩
  unfold IsSol at h
  rw [hx, hz] at h
  norm_num at h
  omega

/-- The same statement as a set equality: exactly one solution has defect `1`. -/
theorem sol_set_defect_one :
    {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2 ∧ p.1 ^ 3 - p.2.2 ^ 2 = 1} = {(1, 1, 0)} := by
  ext ⟨x, y, z⟩
  constructor
  · rintro ⟨hsol, hd⟩
    obtain ⟨rfl, rfl, rfl⟩ := sol_of_defect_one hsol hd
    rfl
  · intro hp
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨by norm_num [IsSol], by norm_num⟩

end Mordell

end CubeSquare
