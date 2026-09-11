import Mathlib

/-!
# On the polynomial values represented by quadratic forms

A complete Lean 4 / Mathlib formalization of the paper *On the polynomial values represented
by quadratic forms* by B. Grechuk and J. Agbanwa, contained in this single file.

The development follows the paper section by section:

* **Section 2** — the set `S₂` of positive integers that are sums of two squares and property
  `(*)`; a Pell-type engine; identities (6) and (7); Propositions 2.2 and 2.3.
* **Section 3** — Algorithm 2.4 specialised to `R(t) = t³ + f`, and Corollaries 3.1 and 3.2.
* **Section 4** — general binary quadratic forms `BQF A B C`, Propositions 4.1, 4.2, 4.4, the
  non-multiplicativity examples, and the degenerate case `Δ = 0`.

The namespace `PolyQF.Main` collects the main results under readable names, the namespace
`Challenge` states them self-containedly in plain Mathlib vocabulary, and the namespace
`Solution` discharges each `Challenge` statement from the development.
-/

/-!
# The set `S₂` of positive integers that are sums of two squares

This file introduces the set `S2` of positive integers representable as a sum of two
integer squares, which is denoted `S₂` in the paper *On the polynomial values represented
by quadratic forms* (Section 2), and establishes the property `(*)` used throughout:

> if `a, b` are positive integers and `S₂` contains two of the integers `a`, `b`, `ab`,
> then `S₂` contains all three of them.
-/

/-!
## Version-stable wrappers

The three lemmas below are `private` local replacements for Mathlib results (membership in a
set-builder set, finiteness of the root set of a nonzero polynomial, and the infinitude of an
infinite set with a finite set removed) whose names have changed across Mathlib versions.
Using them keeps this file free of deprecation warnings.
-/

/-- Membership in a set-builder set: `a ∈ {x | p x}` is `p a`. -/
private theorem mem_setOf_eq' {α : Type*} {a : α} {p : α → Prop} : (a ∈ {x | p x}) = p a := rfl

/-- A nonzero polynomial over an integral domain has only finitely many roots. -/
private theorem finite_setOf_isRoot' {R : Type*} [CommRing R] [IsDomain R] {p : Polynomial R}
    (hp : p ≠ 0) : Set.Finite {x | p.IsRoot x} := by
  refine Set.Finite.subset (Multiset.finite_toSet p.roots) ?_
  intro x hx
  exact Polynomial.mem_roots'.mpr ⟨hp, hx⟩

/-- Removing a finite set from an infinite set leaves an infinite set. -/
private theorem infinite_sdiff_of_finite {α : Type*} {s t : Set α} (hs : s.Infinite)
    (ht : t.Finite) : (s \ t).Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  refine Set.not_infinite.mpr ((hcon.union ht).subset ?_) hs
  intro x hx
  by_cases hxt : x ∈ t
  · exact Set.mem_union_right _ hxt
  · exact Set.mem_union_left _ (Set.mem_sdiff_of_mem hx hxt)

namespace PolyQF

open scoped Classical

/-- `S2 n` says that `n` is a positive integer which is a sum of two integer squares.
This is the set denoted `S₂` in the paper. -/
def S2 (n : ℤ) : Prop := 0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2

lemma S2.pos {n : ℤ} (h : S2 n) : 0 < n := h.1

/-- A natural number is a sum of two natural squares iff it is a sum of two integer squares. -/
lemma nat_sq_add_sq_iff_int {m : ℕ} :
    (∃ x y : ℕ, m = x ^ 2 + y ^ 2) ↔ ∃ y z : ℤ, (m : ℤ) = y ^ 2 + z ^ 2 := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, y, by push_cast; ring⟩
  · rintro ⟨y, z, h⟩
    refine ⟨y.natAbs, z.natAbs, ?_⟩
    have : (m : ℤ) = (y.natAbs : ℤ) ^ 2 + (z.natAbs : ℤ) ^ 2 := by
      rw [h]; simp [sq_abs]
    exact_mod_cast this

/-- Fermat's characterization of the sums of two squares: a nonzero natural number is a sum
of two squares iff every prime `q ≡ 3 (mod 4)` occurs to an even power in it. -/
lemma nat_sumsq_iff {n : ℕ} (hn : n ≠ 0) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q n) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro h q hq hq4
    by_cases hmem : q ∈ n.primeFactors
    · exact h q hmem hq4
    · have : ¬ q ∣ n := by
        intro hdvd
        exact hmem (Nat.mem_primeFactors.2 ⟨hq, hdvd, hn⟩)
      simp [padicValNat.eq_zero_of_not_dvd this]
  · intro h q hq hq4
    exact h q (Nat.prime_of_mem_primeFactors hq) hq4

/-- Characterization of `S2` in terms of `padicValNat`. -/
lemma S2_iff_padicValNat {n : ℤ} (hn : 0 < n) :
    S2 n ↔ ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q n.toNat) := by
  have hne : n.toNat ≠ 0 := by omega
  have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn.le
  constructor
  · intro h
    rw [← nat_sumsq_iff hne, nat_sq_add_sq_iff_int, hcast]
    exact h.2
  · intro h
    refine ⟨hn, ?_⟩
    have := (nat_sumsq_iff hne).2 h
    rw [nat_sq_add_sq_iff_int, hcast] at this
    exact this

/-- The Brahmagupta–Fibonacci identity: `S2` is closed under multiplication. -/
theorem S2.mul {a b : ℤ} (ha : S2 a) (hb : S2 b) : S2 (a * b) := by
  obtain ⟨hapos, y₁, z₁, h₁⟩ := ha
  obtain ⟨hbpos, y₂, z₂, h₂⟩ := hb
  refine ⟨mul_pos hapos hbpos, y₁ * y₂ - z₁ * z₂, y₁ * z₂ + y₂ * z₁, ?_⟩
  subst h₁; subst h₂; ring

/-- Cancellation in `S2`: if `a` and `a * b` are in `S2` and `b > 0`, then `b ∈ S2`. -/
theorem S2.of_mul_right {a b : ℤ} (ha : S2 a) (hb : 0 < b) (hab : S2 (a * b)) : S2 b := by
  have hapos := ha.pos
  rw [S2_iff_padicValNat hapos] at ha
  rw [S2_iff_padicValNat (mul_pos hapos hb)] at hab
  rw [S2_iff_padicValNat hb]
  intro q hq hq4
  have hA : a.toNat ≠ 0 := by omega
  have hB : b.toNat ≠ 0 := by omega
  have hmul : (a * b).toNat = a.toNat * b.toNat := by
    have : ((a * b).toNat : ℤ) = ((a.toNat * b.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (mul_pos hapos hb).le, Int.toNat_of_nonneg hapos.le,
        Int.toNat_of_nonneg hb.le]
    exact_mod_cast this
  have hval : padicValNat q ((a * b).toNat) = padicValNat q a.toNat + padicValNat q b.toNat := by
    rw [hmul]
    have : Fact q.Prime := ⟨hq⟩
    exact padicValNat.mul hA hB
  have h1 := ha q hq hq4
  have h2 := hab q hq hq4
  rw [hval] at h2
  exact (Nat.even_add.mp h2).mp h1

/-- Cancellation in `S2`, other factor. -/
theorem S2.of_mul_left {a b : ℤ} (hb : S2 b) (ha : 0 < a) (hab : S2 (a * b)) : S2 a := by
  refine hb.of_mul_right ha ?_
  rwa [mul_comm] at hab

/-- Property `(*)` of the paper, in the form actually used: if `S₂` contains `a` and `ab`
(with `b` positive) then it contains `b`; and if it contains `a` and `b` then it contains `ab`. -/
theorem S2_star {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    (S2 a → S2 b → S2 (a * b)) ∧ (S2 a → S2 (a * b) → S2 b) ∧ (S2 b → S2 (a * b) → S2 a) :=
  ⟨fun h₁ h₂ => h₁.mul h₂, fun h₁ h₂ => h₁.of_mul_right hb h₂, fun h₁ h₂ => h₁.of_mul_left ha h₂⟩

/-- Four times a member of `S2` is again in `S2`. -/
theorem S2.four_mul {a : ℤ} (ha : S2 a) : S2 (4 * a) :=
  S2.mul ⟨by norm_num, 2, 0, by norm_num⟩ ha

/-- Conversely, if `4 * a ∈ S2` and `a > 0`, then `a ∈ S2`. -/
theorem S2.of_four_mul {a : ℤ} (ha : 0 < a) (h : S2 (4 * a)) : S2 a :=
  S2.of_mul_right ⟨by norm_num, 2, 0, by norm_num⟩ ha h

end PolyQF

/-!
# A Pell-type engine for binary quadratic equations

The two "infinitely many solutions" propositions of the paper (Proposition 2.3 and
Proposition 4.2) both reduce, after completing the square, to the following statement:
if `A > 0` is not a perfect square, `D ≠ 0` and the equation `X ^ 2 - A * V ^ 2 = D` has one
integer solution `(X₀, V₀)`, then it has infinitely many integer solutions, and one may
moreover prescribe `X` and `V` modulo any fixed nonzero modulus `N` (namely `X ≡ X₀`,
`V ≡ V₀`).

This is the classical fact that the solutions of a Pell-like equation can be multiplied by
units of the ring `ℤ[√A]`; the congruence conditions are achieved by choosing a unit which is
congruent to `1` modulo `N`.
-/

namespace PolyQF

/-- If `A` is not a square and `N ≠ 0`, then `A * N ^ 2` is not a square. -/
lemma not_isSquare_mul_sq {A N : ℤ} (hA : ¬ IsSquare A) (hN : N ≠ 0) :
    ¬ IsSquare (A * N ^ 2) := by
  rintro ⟨k, hk⟩
  have hk' : A * N ^ 2 = k ^ 2 := by rw [hk]; ring
  have hdvd : N ^ 2 ∣ k ^ 2 := ⟨A, by linarith [hk']⟩
  have hNk : N ∣ k := (Int.pow_dvd_pow_iff (n := 2) (by norm_num)).1 hdvd
  obtain ⟨m, rfl⟩ := hNk
  have hN2 : (N : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hN
  have hAm : A = m ^ 2 := by
    have h : A * N ^ 2 = m ^ 2 * N ^ 2 := by rw [hk']; ring
    exact mul_right_cancel₀ hN2 h
  exact hA ⟨m, by rw [hAm]; ring⟩

/-- A Pell unit congruent to `1` modulo `N`: there are integers `T, S` with
`T ^ 2 - A * S ^ 2 = 1`, `T ≥ 3`, `N ∣ T - 1`, `N ∣ S` and `S ≠ 0`. -/
lemma exists_pell_unit_congr_one {A N : ℤ} (hA : 0 < A) (hAsq : ¬ IsSquare A) (hN : N ≠ 0) :
    ∃ T S : ℤ, T ^ 2 - A * S ^ 2 = 1 ∧ 3 ≤ T ∧ N ∣ T - 1 ∧ N ∣ S ∧ S ≠ 0 := by
  have hA2 : 2 ≤ A := by
    by_contra hcon
    push Not at hcon
    have hA1 : A = 1 := by omega
    exact hAsq ⟨1, by rw [hA1]; ring⟩
  have hpos : 0 < A * N ^ 2 := by positivity
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hpos (not_isSquare_mul_sq hAsq hN)
  have hy2 : 1 ≤ y ^ 2 := by rcases hy.lt_or_gt with h | h <;> nlinarith
  have hN2 : 1 ≤ N ^ 2 := by rcases hN.lt_or_gt with h | h <;> nlinarith
  have hx2 : 3 ≤ x ^ 2 := by nlinarith
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx2
  refine ⟨2 * x ^ 2 - 1, 2 * x * (N * y), ?_, by nlinarith, ⟨2 * A * N * y ^ 2, ?_⟩,
    ⟨2 * x * y, by ring⟩, ?_⟩
  · linear_combination (4 * x ^ 2) * hxy
  · linear_combination 2 * hxy
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hx0) (mul_ne_zero hN hy)

/-- **Pell engine.** Let `A > 0` be a non-square integer, `D ≠ 0`, and `N ≠ 0`. If the
equation `X ^ 2 - A * V ^ 2 = D` has one integer solution `(X₀, V₀)`, then the set of
`X`-coordinates of solutions `(X, V)` satisfying `X ≡ X₀ (mod N)` and `V ≡ V₀ (mod N)` is
infinite. -/
theorem pell_solutions_infinite {A D N X₀ V₀ : ℤ} (hA : 0 < A) (hAsq : ¬ IsSquare A)
    (hD : D ≠ 0) (hN : N ≠ 0) (h₀ : X₀ ^ 2 - A * V₀ ^ 2 = D) :
    {X : ℤ | ∃ V : ℤ, X ^ 2 - A * V ^ 2 = D ∧ N ∣ X - X₀ ∧ N ∣ V - V₀}.Infinite := by
  obtain ⟨T, S, hTS, hT3, hTN, hSN, hS0⟩ := exists_pell_unit_congr_one hA hAsq hN
  -- One step: from any admissible solution we produce another one with strictly larger `|X|`.
  have step : ∀ X V : ℤ, X ^ 2 - A * V ^ 2 = D → N ∣ X - X₀ → N ∣ V - V₀ →
      ∃ X' V' : ℤ, X' ^ 2 - A * V' ^ 2 = D ∧ N ∣ X' - X₀ ∧ N ∣ V' - V₀ ∧ |X| < |X'| := by
    intro X V hsol hX hV
    -- the two candidates, obtained by multiplying by the unit and by its inverse
    have hsol1 : (X * T + A * V * S) ^ 2 - A * (X * S + V * T) ^ 2 = D := by
      have : (X * T + A * V * S) ^ 2 - A * (X * S + V * T) ^ 2
          = (X ^ 2 - A * V ^ 2) * (T ^ 2 - A * S ^ 2) := by ring
      rw [this, hsol, hTS, mul_one]
    have hsol2 : (X * T - A * V * S) ^ 2 - A * (- (X * S) + V * T) ^ 2 = D := by
      have : (X * T - A * V * S) ^ 2 - A * (- (X * S) + V * T) ^ 2
          = (X ^ 2 - A * V ^ 2) * (T ^ 2 - A * S ^ 2) := by ring
      rw [this, hsol, hTS, mul_one]
    obtain ⟨t, ht⟩ := hTN
    obtain ⟨s, hs⟩ := hSN
    obtain ⟨k, hk⟩ := hX
    obtain ⟨l, hl⟩ := hV
    have hXc1 : N ∣ (X * T + A * V * S) - X₀ :=
      ⟨k + X * t + A * V * s, by linear_combination hk + X * ht + A * V * hs⟩
    have hVc1 : N ∣ (X * S + V * T) - V₀ :=
      ⟨l + X * s + V * t, by linear_combination X * hs + hl + V * ht⟩
    have hXc2 : N ∣ (X * T - A * V * S) - X₀ :=
      ⟨k + X * t - A * V * s, by linear_combination hk + X * ht - A * V * hs⟩
    have hVc2 : N ∣ (- (X * S) + V * T) - V₀ :=
      ⟨l - X * s + V * t, by linear_combination -(X * hs) + hl + V * ht⟩
    -- growth
    by_cases hX0 : X = 0
    · subst hX0
      refine ⟨A * V * S, V * T, by linarith [hsol1], by simpa using hXc1, by simpa using hVc1,
        ?_⟩
      have hV0 : V ≠ 0 := by
        rintro rfl
        simp at hsol
        exact hD hsol.symm
      have : A * V * S ≠ 0 := mul_ne_zero (mul_ne_zero hA.ne' hV0) hS0
      simpa using abs_pos.2 this
    · have habs : |X * T + A * V * S| + |X * T - A * V * S| ≥ 2 * |X| * T := by
        have h1 : |(X * T + A * V * S) + (X * T - A * V * S)| ≤
            |X * T + A * V * S| + |X * T - A * V * S| := abs_add_le _ _
        have h2 : (X * T + A * V * S) + (X * T - A * V * S) = 2 * X * T := by ring
        rw [h2] at h1
        have h3 : |2 * X * T| = 2 * |X| * T := by
          rw [abs_mul, abs_mul, abs_two, abs_of_pos (by linarith : (0:ℤ) < T)]
        linarith [h1, h3.symm.le, h3.le]
      have hXpos : 1 ≤ |X| := by
        have h := abs_pos.2 hX0
        omega
      rcases le_or_gt (|X * T + A * V * S|) |X| with h | h
      · refine ⟨X * T - A * V * S, - (X * S) + V * T, hsol2, hXc2, hVc2, ?_⟩
        nlinarith [habs, hXpos]
      · exact ⟨X * T + A * V * S, X * S + V * T, hsol1, hXc1, hVc1, h⟩
  -- Iterating the step gives solutions with arbitrarily large `|X|`.
  have grow : ∀ n : ℕ, ∃ X V : ℤ, X ^ 2 - A * V ^ 2 = D ∧ N ∣ X - X₀ ∧ N ∣ V - V₀ ∧
      (n : ℤ) ≤ |X| := by
    intro n
    induction n with
    | zero => exact ⟨X₀, V₀, h₀, by simp, by simp, by simp⟩
    | succ n ih =>
        obtain ⟨X, V, hsol, hX, hV, hn⟩ := ih
        obtain ⟨X', V', hsol', hX', hV', hlt⟩ := step X V hsol hX hV
        exact ⟨X', V', hsol', hX', hV', by push_cast; omega⟩
  -- Hence the solution set is unbounded, so infinite.
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun x : ℤ => |x|)).bddAbove
  obtain ⟨X, V, hsol, hX, hV, hbig⟩ := grow (M.toNat + 1)
  have hmem : |X| ≤ M := hM ⟨X, ⟨V, hsol, hX, hV⟩, rfl⟩
  have habs : 0 ≤ |X| := abs_nonneg X
  have hbig' : ((M.toNat + 1 : ℕ) : ℤ) ≤ |X| := hbig
  omega

end PolyQF

/-!
# Elementary tools used in Section 3

Parity facts about sums of two squares, a non-square criterion, and a transfer lemma for
infinite sets.
-/

namespace PolyQF

/-- Every square is `0` or `1` modulo `4`. -/
lemma sq_mod_four (y : ℤ) : ∃ k : ℤ, y ^ 2 = 4 * k ∨ y ^ 2 = 4 * k + 1 := by
  rcases Int.even_or_odd y with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * k, Or.inl (by ring)⟩
  · exact ⟨k * k + k, Or.inr (by ring)⟩

/-- An integer congruent to `3` modulo `4` is not a sum of two squares. -/
lemma not_sq_add_sq_of_three_mod_four {n : ℤ} (hn : n % 4 = 3) : ¬ ∃ y z : ℤ, n = y ^ 2 + z ^ 2 := by
  rintro ⟨y, z, rfl⟩
  obtain ⟨k, hk⟩ := sq_mod_four y
  obtain ⟨l, hl⟩ := sq_mod_four z
  rcases hk with hk | hk <;> rcases hl with hl | hl <;> omega

/-- If `n` is an odd sum of two squares, one of the two squares is odd and the other even. -/
lemma exists_sq_add_sq_odd_even {n : ℤ} (h : ∃ y z : ℤ, n = y ^ 2 + z ^ 2) (hodd : ¬ (2 ∣ n)) :
    ∃ A B : ℤ, n = A ^ 2 + B ^ 2 ∧ ¬ (2 ∣ A) ∧ 2 ∣ B := by
  obtain ⟨y, z, rfl⟩ := h
  rcases Int.even_or_odd y with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases Int.even_or_odd z with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact absurd ⟨2 * a ^ 2 + 2 * b ^ 2, by ring⟩ hodd
  · exact ⟨2 * b + 1, a + a, by ring, by omega, ⟨a, by ring⟩⟩
  · exact ⟨2 * a + 1, b + b, by ring, by omega, ⟨b, by ring⟩⟩
  · exact absurd ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2 + 2 * b + 1, by ring⟩ hodd

/-- If `n` is a sum of two squares and `4 ∣ n`, then both squares are even. -/
lemma exists_sq_add_sq_both_even {n : ℤ} (h : ∃ y z : ℤ, n = y ^ 2 + z ^ 2) (h4 : (4 : ℤ) ∣ n) :
    ∃ A B : ℤ, n = A ^ 2 + B ^ 2 ∧ 2 ∣ A ∧ 2 ∣ B := by
  obtain ⟨y, z, rfl⟩ := h
  obtain ⟨d, hd⟩ := h4
  rcases Int.even_or_odd y with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases Int.even_or_odd z with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨a + a, b + b, by ring, ⟨a, by ring⟩, ⟨b, by ring⟩⟩
  · exfalso
    have h1 : (a + a) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a ^ 2 + b ^ 2 + b) + 1 := by ring
    omega
  · exfalso
    have h1 : (2 * a + 1) ^ 2 + (b + b) ^ 2 = 4 * (a ^ 2 + a + b ^ 2) + 1 := by ring
    omega
  · exfalso
    have h1 : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a ^ 2 + a + b ^ 2 + b) + 2 := by ring
    omega

/-- A number strictly between two consecutive squares is not a perfect square. -/
lemma not_isSquare_of_between {m n : ℤ} (hm : 0 ≤ m) (h1 : m ^ 2 < n) (h2 : n < (m + 1) ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hk2 : n = |k| ^ 2 := by rw [hk]; rw [sq_abs]; ring
  have habs : 0 ≤ |k| := abs_nonneg k
  have hlt1 : m < |k| := by nlinarith
  have hlt2 : |k| < m + 1 := by nlinarith
  omega

/-- If `T` is infinite and contained in the image of `S`, then `S` is infinite. -/
lemma infinite_of_subset_image {α β : Type*} {S : Set α} {T : Set β} (f : α → β)
    (hT : T.Infinite) (h : T ⊆ f '' S) : S.Infinite := by
  intro hS
  exact hT ((hS.image f).subset h)

end PolyQF

/-!
# Section 2 of the paper: the sum of two squares case

This file formalizes:

* the Taylor decomposition (6): for a polynomial `R` and an integer `u` there is a unique
  polynomial `D` with `R = R(u) + R'(u)(X - u) + (X - u)^2 D`;
* identity (7);
* Proposition 2.2, the sufficient condition for `R(Q(x)) ∈ S₂` infinitely often;
* Proposition 2.3, on the infinitude of solutions of `a x^2 + b x + c = v^2`.
-/

namespace PolyQF

open Polynomial

/-! ### Auxiliary facts about infinite sets of integers -/

/-- If a set of pairs is infinite and all its fibres over the first coordinate are finite,
then the set of first coordinates is infinite. -/
lemma infinite_fst_of_infinite {P : ℤ → ℤ → Prop} (h : {p : ℤ × ℤ | P p.1 p.2}.Infinite)
    (hfin : ∀ x : ℤ, {v : ℤ | P x v}.Finite) : {x : ℤ | ∃ v, P x v}.Infinite := by
  intro hXfin
  refine h (Set.Finite.subset (hXfin.biUnion (fun x _ => (Set.finite_singleton x).prod (hfin x)))
    ?_)
  rintro ⟨x, v⟩ hp
  simp only [Set.mem_iUnion, mem_setOf_eq', Set.mem_prod, Set.mem_singleton_iff]
  exact ⟨x, ⟨v, hp⟩, rfl, hp⟩

/-- For a fixed integer `w`, only finitely many integers `v` satisfy `v ^ 2 = w`. -/
lemma finite_setOf_sq_eq (w : ℤ) : {v : ℤ | w = v ^ 2}.Finite := by
  have hne : (X ^ 2 - C w : ℤ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) w
  refine (finite_setOf_isRoot' hne).subset ?_
  intro v hv
  simp only [mem_setOf_eq'] at hv ⊢
  simp [Polynomial.IsRoot, hv]

/-! ### The Taylor decomposition (6) -/

/-- **Identity (6).** For any polynomial `R` and any `u ∈ ℤ` there is a unique polynomial
`Dᵤ` with integer coefficients such that
`R(t) = R(u) + R'(u) (t - u) + (t - u)^2 Dᵤ(t)`. -/
theorem exists_unique_taylorQuot (R : ℤ[X]) (u : ℤ) :
    ∃! D : ℤ[X], R = C (R.eval u) + C (R.derivative.eval u) * (X - C u) + (X - C u) ^ 2 * D := by
  set g : ℤ[X] := taylor u R with hgdef
  set p : ℤ[X] := g.divX with hpdef
  set h : ℤ[X] := p.divX with hhdef
  have c0 : g.coeff 0 = R.eval u := taylor_coeff_zero u R
  have c1 : p.coeff 0 = R.derivative.eval u := by
    rw [hpdef, coeff_divX]; exact taylor_coeff_one u R
  have hg : g = C (R.eval u) + C (R.derivative.eval u) * X + X ^ 2 * h := by
    have h1 : X * p + C (g.coeff 0) = g := X_mul_divX_add g
    have h2 : X * h + C (p.coeff 0) = p := X_mul_divX_add p
    rw [c0] at h1
    rw [c1] at h2
    rw [← h1, ← h2]; ring
  have hcomp : g.comp (X - C u) = R := by
    rw [hgdef, taylor_apply, comp_assoc]
    simp
  have hex : R = C (R.eval u) + C (R.derivative.eval u) * (X - C u)
      + (X - C u) ^ 2 * (h.comp (X - C u)) := by
    conv_lhs => rw [← hcomp, hg]
    simp [add_comp, mul_comp, pow_comp]
  refine ⟨h.comp (X - C u), hex, ?_⟩
  intro D hD
  have hcancel : (X - C u) ^ 2 * D = (X - C u) ^ 2 * (h.comp (X - C u)) := by
    linear_combination hex - hD
  exact mul_left_cancel₀ (pow_ne_zero 2 (X_sub_C_ne_zero u)) hcancel

/-- **Identity (7).** Multiplying the Taylor identity (6) by `4 R(u)` and rearranging:
`4 m (m + r (t - u) + (t-u)^2 d) = (2m + r (t - u))^2 + (t - u)^2 (4 m d - r^2)`. -/
theorem identity_seven (m r d t u : ℤ) :
    4 * m * (m + r * (t - u) + (t - u) ^ 2 * d)
      = (2 * m + r * (t - u)) ^ 2 + (t - u) ^ 2 * (4 * m * d - r ^ 2) := by
  ring

/-- The evaluated form of the Taylor identity (6). -/
lemma eval_taylorQuot {R Du : ℤ[X]} {u : ℤ}
    (hDu : R = C (R.eval u) + C (R.derivative.eval u) * (X - C u) + (X - C u) ^ 2 * Du)
    (t : ℤ) :
    R.eval t = R.eval u + R.derivative.eval u * (t - u) + (t - u) ^ 2 * Du.eval t := by
  conv_lhs => rw [hDu]
  simp

/-! ### Proposition 2.2 -/

/-- **Proposition 2.2.** Let `R` and `Q` be non-constant polynomials with integer coefficients
and let `u ∈ ℤ` satisfy `R(u) ∈ S₂`. Let `Dᵤ` be defined by (6). If the auxiliary equation
`4 R(u) Dᵤ(Q(x)) - R'(u)^2 = v^2` has infinitely many integer solutions `(x, v)`, then
`R(Q(x)) ∈ S₂` for infinitely many integers `x`. -/
theorem prop_2_2 {R Q : ℤ[X]} (hR : 0 < R.natDegree) (hQ : 0 < Q.natDegree) {u : ℤ}
    (hRu : S2 (R.eval u)) {Du : ℤ[X]}
    (hDu : R = C (R.eval u) + C (R.derivative.eval u) * (X - C u) + (X - C u) ^ 2 * Du)
    (hinf : {p : ℤ × ℤ |
      4 * R.eval u * Du.eval (Q.eval p.1) - R.derivative.eval u ^ 2 = p.2 ^ 2}.Infinite) :
    {x : ℤ | S2 (R.eval (Q.eval x))}.Infinite := by
  have hx : {x : ℤ |
      ∃ v : ℤ, 4 * R.eval u * Du.eval (Q.eval x) - R.derivative.eval u ^ 2 = v ^ 2}.Infinite :=
    infinite_fst_of_infinite hinf fun _ => finite_setOf_sq_eq _
  have hcompne : R.comp Q ≠ 0 := by
    intro hzero
    have hdeg : (R.comp Q).natDegree = R.natDegree * Q.natDegree := natDegree_comp
    rw [hzero, natDegree_zero] at hdeg
    have hpos : 0 < R.natDegree * Q.natDegree := by positivity
    omega
  have hroot : {x : ℤ | R.eval (Q.eval x) = 0}.Finite := by
    have hset : {x : ℤ | R.eval (Q.eval x) = 0} = {x : ℤ | (R.comp Q).IsRoot x} := by
      ext x; simp [Polynomial.IsRoot, eval_comp]
    rw [hset]
    exact finite_setOf_isRoot' hcompne
  refine (infinite_sdiff_of_finite hx hroot).mono ?_
  rintro x ⟨⟨v, hv⟩, hne⟩
  simp only [mem_setOf_eq'] at hne ⊢
  set t : ℤ := Q.eval x with ht
  set m : ℤ := R.eval u with hm
  set r : ℤ := R.derivative.eval u with hr
  have hEval : R.eval t = m + r * (t - u) + (t - u) ^ 2 * Du.eval t := eval_taylorQuot hDu t
  have key : 4 * m * R.eval t = (2 * m + r * (t - u)) ^ 2 + ((t - u) * v) ^ 2 := by
    rw [hEval]
    linear_combination ((t - u) ^ 2) * hv
  have hmpos : 0 < m := hRu.pos
  have hnonneg : 0 ≤ 4 * m * R.eval t := by rw [key]; positivity
  have hne' : 4 * m * R.eval t ≠ 0 := by
    exact mul_ne_zero (by positivity) hne
  have hprodpos : 0 < 4 * m * R.eval t := lt_of_le_of_ne hnonneg (Ne.symm hne')
  have hRpos : 0 < R.eval t := by nlinarith [hprodpos, hmpos]
  exact hRu.four_mul.of_mul_right hRpos ⟨hprodpos, _, _, key⟩

/-! ### Proposition 2.3 -/

/-- **Proposition 2.3.** Let `a, b, c ∈ ℤ` be such that (a) either `a = 0`, or `a > 0` and `a`
is not a perfect square, (b) `b^2 - 4ac ≠ 0`, and (c) the equation `a x^2 + b x + c = v^2`
has an integer solution `(x₀, v₀)`. Then this equation has infinitely many integer solutions
`(x, v)` with infinitely many distinct values of `x`. -/
theorem prop_2_3 {a b c : ℤ} (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a)) (hb : b ^ 2 - 4 * a * c ≠ 0)
    {x₀ v₀ : ℤ} (hsol : a * x₀ ^ 2 + b * x₀ + c = v₀ ^ 2) :
    {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite := by
  rcases ha with rfl | ⟨hapos, hasq⟩
  · -- the linear case `a = 0`
    have hb0 : b ≠ 0 := by
      intro h; apply hb; rw [h]; ring
    have hb2 : 1 ≤ b ^ 2 := by rcases hb0.lt_or_gt with h | h <;> nlinarith
    have hsol0 : b * x₀ + c = v₀ ^ 2 := by linear_combination hsol
    set f : ℤ → ℤ := fun k => x₀ + 2 * v₀ * k * b + k ^ 2 * b ^ 3 with hf
    have hval : ∀ k : ℤ, b * f k + c = (v₀ + k * b ^ 2) ^ 2 := by
      intro k; simp only [hf]; linear_combination hsol0
    have hvpos : ∀ k : ℤ, |v₀| + 1 ≤ k → 0 < v₀ + k * b ^ 2 := by
      intro k hk
      have h1 : |v₀| + 1 ≤ k := hk
      have h2 : -v₀ ≤ |v₀| := neg_le_abs v₀
      nlinarith [abs_nonneg v₀]
    have hinj : Set.InjOn f (Set.Ici (|v₀| + 1)) := by
      intro k hk k' hk' heq
      have h1 : (v₀ + k * b ^ 2) ^ 2 = (v₀ + k' * b ^ 2) ^ 2 := by
        rw [← hval k, ← hval k', heq]
      have h2 : 0 < v₀ + k * b ^ 2 := hvpos k hk
      have h3 : 0 < v₀ + k' * b ^ 2 := hvpos k' hk'
      have h4 : v₀ + k * b ^ 2 = v₀ + k' * b ^ 2 := by nlinarith
      have h5 : (k - k') * b ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 h5 with h | h
      · linarith [h]
      · omega
    refine ((Set.Ici_infinite (|v₀| + 1)).image hinj).mono ?_
    rintro _ ⟨k, _, rfl⟩
    exact ⟨v₀ + k * b ^ 2, by have := hval k; linarith⟩
  · -- the genuinely quadratic case
    have h4a : (0 : ℤ) < 4 * a := by linarith
    have h4asq : ¬ IsSquare (4 * a) := by
      rintro ⟨k, hk⟩
      have hkeven : Even k := by
        rcases Int.even_or_odd k with he | ho
        · exact he
        · exfalso
          obtain ⟨j, rfl⟩ := ho
          have h2 : 4 * a = 4 * (j * j + j) + 1 := by linarith [hk]
          omega
      obtain ⟨j, rfl⟩ := hkeven
      exact hasq ⟨j, by linarith [hk]⟩
    have hN : (2 * a : ℤ) ≠ 0 := by positivity
    have hX₀ : (2 * a * x₀ + b) ^ 2 - 4 * a * v₀ ^ 2 = b ^ 2 - 4 * a * c := by
      linear_combination (4 * a) * hsol
    have hinf := pell_solutions_infinite h4a h4asq hb hN hX₀
    have hinj : Set.InjOn (fun X : ℤ => (X - b) / (2 * a))
        {X : ℤ | ∃ V : ℤ, X ^ 2 - 4 * a * V ^ 2 = b ^ 2 - 4 * a * c ∧
          2 * a ∣ X - (2 * a * x₀ + b) ∧ 2 * a ∣ V - v₀} := by
      rintro X ⟨V, -, hXc, -⟩ X' ⟨V', -, hXc', -⟩ heq
      obtain ⟨k, hk⟩ := hXc
      obtain ⟨k', hk'⟩ := hXc'
      have hd : 2 * a ∣ X - b := ⟨k + x₀, by linarith⟩
      have hd' : 2 * a ∣ X' - b := ⟨k' + x₀, by linarith⟩
      have e1 : 2 * a * ((X - b) / (2 * a)) = X - b := Int.mul_ediv_cancel' hd
      have e2 : 2 * a * ((X' - b) / (2 * a)) = X' - b := Int.mul_ediv_cancel' hd'
      simp only at heq
      rw [heq] at e1
      linarith [e1, e2]
    refine (hinf.image hinj).mono ?_
    rintro _ ⟨X, ⟨V, hXV, hXc, -⟩, rfl⟩
    obtain ⟨k, hk⟩ := hXc
    have hd : 2 * a ∣ X - b := ⟨k + x₀, by linarith⟩
    have e1 : 2 * a * ((X - b) / (2 * a)) = X - b := Int.mul_ediv_cancel' hd
    set x : ℤ := (X - b) / (2 * a) with hxdef
    have hX : X = 2 * a * x + b := by linarith
    refine ⟨V, ?_⟩
    rw [hX] at hXV
    have h4 : (4 * a) * (a * x ^ 2 + b * x + c - V ^ 2) = 0 := by linear_combination hXV
    have := mul_eq_zero.1 h4
    rcases this with h | h
    · exact absurd h (by positivity)
    · linarith

/-- The pair version of Proposition 2.3: the solution set itself is infinite. -/
theorem prop_2_3_pairs {a b c : ℤ} (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a))
    (hb : b ^ 2 - 4 * a * c ≠ 0) {x₀ v₀ : ℤ} (hsol : a * x₀ ^ 2 + b * x₀ + c = v₀ ^ 2) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + b * p.1 + c = p.2 ^ 2}.Infinite := by
  intro hfin
  refine prop_2_3 ha hb hsol ((hfin.image Prod.fst).subset ?_)
  rintro x ⟨v, hv⟩
  exact ⟨(x, v), hv, rfl⟩

end PolyQF

/-!
# Section 3: the two specializations of Algorithm 2.4 used in the applications

Both specializations use `R(t) = t ^ 3 + f`, for which `R(u) = u ^ 3 + f`, `R'(u) = 3u^2`
and `Dᵤ(t) = t + 2u`, so that the auxiliary equation (8) becomes equation (11) of the paper:
`4 (u ^ 3 + f) (Q(x) + 2u) - 9u^4 = v^2`.

We record the case `Q(x) = x ^ 2` (giving `P(x) = x ^ 6 + f`) and the case `Q(w) = 4w^2`
(giving `P(w) = (2w) ^ 6 + f`, i.e. the restriction to even `x`).
-/

namespace PolyQF

open Polynomial

section Specialization

variable {f u : ℤ}

/-- The Taylor decomposition (6) for `R(t) = t ^ 3 + f`: here `Dᵤ(t) = t + 2u`. -/
lemma taylor_cubic (f u : ℤ) :
    (X ^ 3 + C f : ℤ[X]) = C ((X ^ 3 + C f : ℤ[X]).eval u)
      + C ((derivative (X ^ 3 + C f : ℤ[X])).eval u) * (X - C u)
      + (X - C u) ^ 2 * (X + C (2 * u)) := by
  have h1 : (X ^ 3 + C f : ℤ[X]).eval u = u ^ 3 + f := by simp
  have h2 : (derivative (X ^ 3 + C f : ℤ[X])).eval u = 3 * u ^ 2 := by
    simp
  rw [h1, h2]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- **Algorithm 2.4 for `P(x) = x ^ 6 + f`.** If `u ^ 3 + f ∈ S₂` and the auxiliary equation
(11), `4 (u ^ 3 + f) x ^ 2 - u (u ^ 3 - 8 f) = v ^ 2`, has infinitely many integer solutions,
then `x ^ 6 + f ∈ S₂` for infinitely many integers `x`. -/
theorem S2_sixth_power_infinite (hS : S2 (u ^ 3 + f))
    (hinf : {p : ℤ × ℤ | 4 * (u ^ 3 + f) * p.1 ^ 2 - u * (u ^ 3 - 8 * f) = p.2 ^ 2}.Infinite) :
    {x : ℤ | S2 (x ^ 6 + f)}.Infinite := by
  have h1 : (X ^ 3 + C f : ℤ[X]).eval u = u ^ 3 + f := by simp
  have h2 : (derivative (X ^ 3 + C f : ℤ[X])).eval u = 3 * u ^ 2 := by
    simp
  have hRdeg : 0 < (X ^ 3 + C f : ℤ[X]).natDegree := by
    have : (X ^ 3 + C f : ℤ[X]).natDegree = 3 := by compute_degree!
    omega
  have hQdeg : 0 < (X ^ 2 : ℤ[X]).natDegree := by
    rw [natDegree_X_pow]; norm_num
  have key := prop_2_2 (R := X ^ 3 + C f) (Q := X ^ 2) (u := u) (Du := X + C (2 * u))
    hRdeg hQdeg (by rwa [h1]) (taylor_cubic f u) ?_
  · refine key.mono ?_
    intro x hx
    simp only [mem_setOf_eq', eval_add, eval_pow, eval_X, eval_C] at hx ⊢
    have : ((x ^ 2) ^ 3 + f) = x ^ 6 + f := by ring
    rwa [this] at hx
  · refine hinf.mono ?_
    rintro p hp
    simp only [mem_setOf_eq', eval_add, eval_pow, eval_X, eval_C, h1, h2] at hp ⊢
    linear_combination hp

/-- **Algorithm 2.4 for even values**: with `Q(w) = 4 w ^ 2` we get `P(w) = (2w) ^ 6 + f`.
If `u ^ 3 + f ∈ S₂` and `16 (u ^ 3 + f) w ^ 2 - u (u ^ 3 - 8 f) = v ^ 2` has infinitely many
integer solutions, then `(2w) ^ 6 + f ∈ S₂` for infinitely many integers `w`. -/
theorem S2_sixth_power_even_infinite (hS : S2 (u ^ 3 + f))
    (hinf : {p : ℤ × ℤ | 16 * (u ^ 3 + f) * p.1 ^ 2 - u * (u ^ 3 - 8 * f) = p.2 ^ 2}.Infinite) :
    {w : ℤ | S2 ((2 * w) ^ 6 + f)}.Infinite := by
  have h1 : (X ^ 3 + C f : ℤ[X]).eval u = u ^ 3 + f := by simp
  have h2 : (derivative (X ^ 3 + C f : ℤ[X])).eval u = 3 * u ^ 2 := by
    simp
  have hRdeg : 0 < (X ^ 3 + C f : ℤ[X]).natDegree := by
    have : (X ^ 3 + C f : ℤ[X]).natDegree = 3 := by compute_degree!
    omega
  have hQdeg : 0 < (C 4 * X ^ 2 : ℤ[X]).natDegree := by
    have : (C 4 * X ^ 2 : ℤ[X]).natDegree = 2 := by compute_degree!
    omega
  have key := prop_2_2 (R := X ^ 3 + C f) (Q := C 4 * X ^ 2) (u := u) (Du := X + C (2 * u))
    hRdeg hQdeg (by rwa [h1]) (taylor_cubic f u) ?_
  · refine key.mono ?_
    intro x hx
    simp only [mem_setOf_eq', eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx ⊢
    have : ((4 * x ^ 2) ^ 3 + f) = (2 * x) ^ 6 + f := by ring
    rwa [this] at hx
  · refine hinf.mono ?_
    rintro p hp
    simp only [mem_setOf_eq', eval_add, eval_mul, eval_pow, eval_X, eval_C, h1, h2] at hp ⊢
    linear_combination hp

end Specialization

end PolyQF

/-!
# Section 3: application to the shortest open equations

We prove that `x ^ 6 + f` is a sum of two squares infinitely often for `f ∈ {8, 5, -3, -4}`
(for `f ∈ {8, 5, -3}` even for infinitely many *even* `x`), and deduce Corollary 3.1 and
Corollary 3.2 of the paper: each of the equations

* `y ^ 2 + x ^ 3 y + z ^ 2 + 1 = 0`      (equation (2)),
* `y ^ 2 + x ^ 3 y + z ^ 2 - 2 = 0`      (equation (13)),
* `y ^ 2 + x ^ 3 y + z ^ 2 + z - 1 = 0`  (equation (14)),
* `y ^ 2 + x ^ 3 y + z ^ 2 + z + 1 = 0`  (equation (15)),
* `y ^ 2 + x ^ 3 y + y + z ^ 2 + 1 = 0`  (equation (16))

has infinitely many integer solutions.
-/

namespace PolyQF

open Polynomial

/-! ### The auxiliary equations -/

/-- Specialization of Proposition 2.3 to the equations `a x ^ 2 + c = v ^ 2` occurring in
Section 3. -/
lemma aux_pairs_infinite {a c x₀ v₀ : ℤ} (hapos : 0 < a) (hasq : ¬ IsSquare a)
    (hac : a * c ≠ 0) (hsol : a * x₀ ^ 2 + c = v₀ ^ 2) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + c = p.2 ^ 2}.Infinite := by
  have hb : (0 : ℤ) ^ 2 - 4 * a * c ≠ 0 := by
    intro h
    apply hac
    have : (4 : ℤ) * (a * c) = 0 := by linarith [h]
    linarith [this]
  have h := prop_2_3_pairs (a := a) (b := 0) (c := c) (Or.inr ⟨hapos, hasq⟩) hb
    (x₀ := x₀) (v₀ := v₀) (by linear_combination hsol)
  refine h.mono ?_
  rintro p hp
  simp only [mem_setOf_eq'] at hp ⊢
  linear_combination hp

/-! ### `x ^ 6 + f ∈ S₂` infinitely often -/

/-- `x ^ 6 - 4` is a sum of two squares for infinitely many integers `x`
(Algorithm 2.4 with `u = 162`). -/
theorem S2_x6_sub_4_infinite : {x : ℤ | S2 (x ^ 6 - 4)}.Infinite := by
  have hS : S2 ((162 : ℤ) ^ 3 + (-4)) := ⟨by norm_num, 350, 2032, by norm_num⟩
  have haux : {p : ℤ × ℤ | (17006096 : ℤ) * p.1 ^ 2 + (-688752720) = p.2 ^ 2}.Infinite :=
    aux_pairs_infinite (by norm_num)
      (not_isSquare_of_between (m := 4123) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
      (x₀ := 22108343594783571) (v₀ := 91171377945572295096) (by norm_num)
  have hinf : {p : ℤ × ℤ |
      4 * ((162 : ℤ) ^ 3 + (-4)) * p.1 ^ 2 - 162 * ((162 : ℤ) ^ 3 - 8 * (-4)) = p.2 ^ 2}.Infinite := by
    refine haux.mono ?_
    rintro p hp
    simp only [mem_setOf_eq'] at hp ⊢
    linear_combination hp
  have := S2_sixth_power_infinite hS hinf
  refine this.mono ?_
  intro x hx
  simp only [mem_setOf_eq'] at hx ⊢
  have he : x ^ 6 + (-4) = x ^ 6 - 4 := by ring
  rwa [he] at hx

/-- For `f ∈ {8, 5, -3}` we get infinitely many *even* `x` with `x ^ 6 + f ∈ S₂`.
Here `f = 8`, `u = 8`. -/
theorem S2_x6_add_8_even_infinite : {x : ℤ | S2 (x ^ 6 + 8) ∧ (2 : ℤ) ∣ x}.Infinite := by
  have hS : S2 ((8 : ℤ) ^ 3 + 8) := ⟨by norm_num, 22, 6, by norm_num⟩
  have haux : {p : ℤ × ℤ | (8320 : ℤ) * p.1 ^ 2 + (-3584) = p.2 ^ 2}.Infinite :=
    aux_pairs_infinite (by norm_num)
      (not_isSquare_of_between (m := 91) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (x₀ := 6) (v₀ := 544) (by norm_num)
  have hinf : {p : ℤ × ℤ |
      16 * ((8 : ℤ) ^ 3 + 8) * p.1 ^ 2 - 8 * ((8 : ℤ) ^ 3 - 8 * 8) = p.2 ^ 2}.Infinite := by
    refine haux.mono ?_
    rintro p hp
    simp only [mem_setOf_eq'] at hp ⊢
    linear_combination hp
  have hw := S2_sixth_power_even_infinite hS hinf
  refine (hw.image (f := fun w : ℤ => 2 * w) ?_).mono ?_
  · intro a _ b _ hab
    simpa using hab
  · rintro _ ⟨w, hw', rfl⟩
    exact ⟨hw', ⟨w, rfl⟩⟩

/-- Here `f = 5`, `u = 2`. -/
theorem S2_x6_add_5_even_infinite : {x : ℤ | S2 (x ^ 6 + 5) ∧ (2 : ℤ) ∣ x}.Infinite := by
  have hS : S2 ((2 : ℤ) ^ 3 + 5) := ⟨by norm_num, 3, 2, by norm_num⟩
  have haux : {p : ℤ × ℤ | (208 : ℤ) * p.1 ^ 2 + 64 = p.2 ^ 2}.Infinite :=
    aux_pairs_infinite (by norm_num)
      (not_isSquare_of_between (m := 14) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (x₀ := 3) (v₀ := 44) (by norm_num)
  have hinf : {p : ℤ × ℤ |
      16 * ((2 : ℤ) ^ 3 + 5) * p.1 ^ 2 - 2 * ((2 : ℤ) ^ 3 - 8 * 5) = p.2 ^ 2}.Infinite := by
    refine haux.mono ?_
    rintro p hp
    simp only [mem_setOf_eq'] at hp ⊢
    linear_combination hp
  have hw := S2_sixth_power_even_infinite hS hinf
  refine (hw.image (f := fun w : ℤ => 2 * w) ?_).mono ?_
  · intro a _ b _ hab
    simpa using hab
  · rintro _ ⟨w, hw', rfl⟩
    exact ⟨hw', ⟨w, rfl⟩⟩

/-- Here `f = -3`, `u = 2`. -/
theorem S2_x6_sub_3_even_infinite : {x : ℤ | S2 (x ^ 6 - 3) ∧ (2 : ℤ) ∣ x}.Infinite := by
  have hS : S2 ((2 : ℤ) ^ 3 + (-3)) := ⟨by norm_num, 2, 1, by norm_num⟩
  have haux : {p : ℤ × ℤ | (80 : ℤ) * p.1 ^ 2 + (-64) = p.2 ^ 2}.Infinite :=
    aux_pairs_infinite (by norm_num)
      (not_isSquare_of_between (m := 8) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (x₀ := 1) (v₀ := 4) (by norm_num)
  have hinf : {p : ℤ × ℤ |
      16 * ((2 : ℤ) ^ 3 + (-3)) * p.1 ^ 2 - 2 * ((2 : ℤ) ^ 3 - 8 * (-3)) = p.2 ^ 2}.Infinite := by
    refine haux.mono ?_
    rintro p hp
    simp only [mem_setOf_eq'] at hp ⊢
    linear_combination hp
  have hw := S2_sixth_power_even_infinite hS hinf
  refine (hw.image (f := fun w : ℤ => 2 * w) ?_).mono ?_
  · intro a _ b _ hab
    simpa using hab
  · rintro _ ⟨w, hw', rfl⟩
    simp only [mem_setOf_eq'] at hw'
    refine ⟨?_, ⟨w, rfl⟩⟩
    have he : (2 * w) ^ 6 + (-3) = (2 * w) ^ 6 - 3 := by ring
    rwa [he] at hw'

/-! ### Corollary 3.1 -/

/-- Any `x` with `x ^ 6 - 4 ∈ S₂` is odd. -/
lemma odd_of_S2_x6_sub_4 {x : ℤ} (hx : S2 (x ^ 6 - 4)) : ¬ (2 ∣ x) := by
  rintro ⟨w, rfl⟩
  have hpos : 0 < (2 * w) ^ 6 - 4 := hx.pos
  have hfac : (2 * w) ^ 6 - 4 = 4 * (16 * w ^ 6 - 1) := by ring
  have hpos' : 0 < 16 * w ^ 6 - 1 := by nlinarith [hpos]
  rw [hfac] at hx
  have h2 : S2 (16 * w ^ 6 - 1) := S2.of_four_mul hpos' hx
  refine not_sq_add_sq_of_three_mod_four (n := 16 * w ^ 6 - 1) ?_ h2.2
  have : 16 * w ^ 6 - 1 = 4 * (4 * w ^ 6 - 1) + 3 := by ring
  omega

/-- **Corollary 3.1.** Equation (2), `y ^ 2 + x ^ 3 y + z ^ 2 + 1 = 0`, has infinitely many
integer solutions. -/
theorem cor_3_1 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  refine infinite_of_subset_image (fun p : ℤ × ℤ × ℤ => p.1) S2_x6_sub_4_infinite ?_
  intro x hx
  simp only [mem_setOf_eq'] at hx
  have hxodd : ¬ (2 ∣ x) := odd_of_S2_x6_sub_4 hx
  have hx3odd : ¬ (2 ∣ x ^ 3) := by
    intro h
    exact hxodd (Int.Prime.dvd_pow' (by norm_num) h)
  have hodd : ¬ (2 ∣ x ^ 6 - 4) := by
    intro h
    obtain ⟨j, hj⟩ := h
    have h6 : x ^ 6 = (x ^ 3) ^ 2 := by ring
    obtain ⟨k, hk⟩ : ∃ k, x ^ 3 = 2 * k + 1 := by
      rcases Int.even_or_odd (x ^ 3) with ⟨k, hkk⟩ | ⟨k, hkk⟩
      · exact absurd ⟨k, by omega⟩ hx3odd
      · exact ⟨k, hkk⟩
    rw [h6, hk] at hj
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    omega
  obtain ⟨A, B, hAB, hAodd, hBeven⟩ := exists_sq_add_sq_odd_even hx.2 hodd
  obtain ⟨z, hz⟩ := hBeven
  obtain ⟨y, hy⟩ : ∃ y : ℤ, A = x ^ 3 + 2 * y := by
    obtain ⟨k, hk⟩ : ∃ k, A = 2 * k + 1 := by
      rcases Int.even_or_odd A with ⟨k, hkk⟩ | ⟨k, hkk⟩
      · exact absurd ⟨k, by omega⟩ hAodd
      · exact ⟨k, hkk⟩
    obtain ⟨j, hj⟩ : ∃ j, x ^ 3 = 2 * j + 1 := by
      rcases Int.even_or_odd (x ^ 3) with ⟨j, hjj⟩ | ⟨j, hjj⟩
      · exact absurd ⟨j, by omega⟩ hx3odd
      · exact ⟨j, hjj⟩
    exact ⟨k - j, by omega⟩
  refine ⟨(x, y, z), ?_, rfl⟩
  simp only [mem_setOf_eq']
  have h4 : 4 * (y ^ 2 + x ^ 3 * y + z ^ 2 + 1) = 0 := by
    rw [hy, hz] at hAB
    linear_combination -hAB
  linarith

/-! ### Corollary 3.2 -/

/-- **Corollary 3.2, equation (13).** `y ^ 2 + x ^ 3 y + z ^ 2 - 2 = 0` has infinitely many
integer solutions. -/
theorem cor_3_2_eq13 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite := by
  refine infinite_of_subset_image (fun p : ℤ × ℤ × ℤ => p.1) S2_x6_add_8_even_infinite ?_
  rintro x ⟨hx, w, rfl⟩
  have h4 : (4 : ℤ) ∣ (2 * w) ^ 6 + 8 := ⟨16 * w ^ 6 + 2, by ring⟩
  obtain ⟨A, B, hAB, hAe, hBe⟩ := exists_sq_add_sq_both_even hx.2 h4
  obtain ⟨z, hz⟩ := hBe
  obtain ⟨a, ha⟩ := hAe
  obtain ⟨y, hy⟩ : ∃ y : ℤ, A = (2 * w) ^ 3 + 2 * y := ⟨a - 4 * w ^ 3, by rw [ha]; ring⟩
  refine ⟨(2 * w, y, z), ?_, rfl⟩
  simp only [mem_setOf_eq']
  have h4' : 4 * (y ^ 2 + (2 * w) ^ 3 * y + z ^ 2 - 2) = 0 := by
    rw [hy, hz] at hAB
    linear_combination -hAB
  linarith

/-- **Corollary 3.2, equation (14).** `y ^ 2 + x ^ 3 y + z ^ 2 + z - 1 = 0` has infinitely many
integer solutions. -/
theorem cor_3_2_eq14 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite := by
  refine infinite_of_subset_image (fun p : ℤ × ℤ × ℤ => p.1) S2_x6_add_5_even_infinite ?_
  rintro x ⟨hx, w, rfl⟩
  have hodd : ¬ (2 ∣ (2 * w) ^ 6 + 5) := by
    have h : (2 * w) ^ 6 + 5 = 2 * (32 * w ^ 6 + 2) + 1 := by ring
    omega
  obtain ⟨A, B, hAB, hAodd, hBe⟩ := exists_sq_add_sq_odd_even hx.2 hodd
  -- here the *even* square is `B`, and the odd one is `A`
  obtain ⟨b, hb⟩ := hBe
  obtain ⟨y, hy⟩ : ∃ y : ℤ, B = (2 * w) ^ 3 + 2 * y := ⟨b - 4 * w ^ 3, by rw [hb]; ring⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, A = 2 * z + 1 := by
    rcases Int.even_or_odd A with ⟨k, hkk⟩ | ⟨k, hkk⟩
    · exact absurd ⟨k, by omega⟩ hAodd
    · exact ⟨k, hkk⟩
  refine ⟨(2 * w, y, z), ?_, rfl⟩
  simp only [mem_setOf_eq']
  have h4' : 4 * (y ^ 2 + (2 * w) ^ 3 * y + z ^ 2 + z - 1) = 0 := by
    rw [hy, hz] at hAB
    linear_combination -hAB
  linarith

/-- **Corollary 3.2, equation (15).** `y ^ 2 + x ^ 3 y + z ^ 2 + z + 1 = 0` has infinitely many
integer solutions. -/
theorem cor_3_2_eq15 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite := by
  refine infinite_of_subset_image (fun p : ℤ × ℤ × ℤ => p.1) S2_x6_sub_3_even_infinite ?_
  rintro x ⟨hx, w, rfl⟩
  have hodd : ¬ (2 ∣ (2 * w) ^ 6 - 3) := by
    have h : (2 * w) ^ 6 - 3 = 2 * (32 * w ^ 6 - 2) + 1 := by ring
    omega
  obtain ⟨A, B, hAB, hAodd, hBe⟩ := exists_sq_add_sq_odd_even hx.2 hodd
  obtain ⟨b, hb⟩ := hBe
  obtain ⟨y, hy⟩ : ∃ y : ℤ, B = (2 * w) ^ 3 + 2 * y := ⟨b - 4 * w ^ 3, by rw [hb]; ring⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, A = 2 * z + 1 := by
    rcases Int.even_or_odd A with ⟨k, hkk⟩ | ⟨k, hkk⟩
    · exact absurd ⟨k, by omega⟩ hAodd
    · exact ⟨k, hkk⟩
  refine ⟨(2 * w, y, z), ?_, rfl⟩
  simp only [mem_setOf_eq']
  have h4' : 4 * (y ^ 2 + (2 * w) ^ 3 * y + z ^ 2 + z + 1) = 0 := by
    rw [hy, hz] at hAB
    linear_combination -hAB
  linarith

/-- Either the nonnegative or the nonpositive part of an infinite set of integers is
infinite. -/
lemma infinite_nonneg_or_nonpos {S : Set ℤ} (h : S.Infinite) :
    (S ∩ Set.Ici 0).Infinite ∨ (S ∩ Set.Iic 0).Infinite := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine h ((h1.union h2).subset ?_)
  intro x hx
  rcases le_or_gt 0 x with hx0 | hx0
  · exact Or.inl ⟨hx, hx0⟩
  · exact Or.inr ⟨hx, le_of_lt hx0⟩

/-- `(x ^ 3 + 1) ^ 2 - 4 ∈ S₂` for infinitely many (even) integers `x`. -/
theorem S2_cube_add_one_sq_sub_4_infinite :
    {x : ℤ | S2 ((x ^ 3 + 1) ^ 2 - 4) ∧ (2 : ℤ) ∣ x}.Infinite := by
  have hbase := S2_x6_sub_3_even_infinite
  have key : ∀ w : ℤ, (S2 (w ^ 6 - 3) ∧ (2 : ℤ) ∣ w) →
      S2 (((-w ^ 2) ^ 3 + 1) ^ 2 - 4) ∧ (2 : ℤ) ∣ (-w ^ 2) := by
    rintro w ⟨hw, k, rfl⟩
    have hfac : (((-(2 * k) ^ 2) ^ 3 + 1) ^ 2 - 4)
        = ((2 * k) ^ 6 - 3) * ((2 * k) ^ 6 + 1) := by ring
    refine ⟨?_, ⟨-(2 * k ^ 2), by ring⟩⟩
    rw [hfac]
    exact hw.mul ⟨by positivity, (2 * k) ^ 3, 1, by ring⟩
  rcases infinite_nonneg_or_nonpos hbase with hpos | hneg
  · refine ((hpos.image (f := fun w : ℤ => -w ^ 2) ?_)).mono ?_
    · rintro a ⟨-, ha⟩ b ⟨-, hb⟩ hab
      simp only [Set.mem_Ici] at ha hb
      simp only [neg_inj] at hab
      nlinarith
    · rintro _ ⟨w, ⟨hw, -⟩, rfl⟩
      exact key w hw
  · refine ((hneg.image (f := fun w : ℤ => -w ^ 2) ?_)).mono ?_
    · rintro a ⟨-, ha⟩ b ⟨-, hb⟩ hab
      simp only [Set.mem_Iic] at ha hb
      simp only [neg_inj] at hab
      nlinarith
    · rintro _ ⟨w, ⟨hw, -⟩, rfl⟩
      exact key w hw

/-- **Corollary 3.2, equation (16).** `y ^ 2 + x ^ 3 y + y + z ^ 2 + 1 = 0` has infinitely many
integer solutions. -/
theorem cor_3_2_eq16 :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite := by
  refine infinite_of_subset_image (fun p : ℤ × ℤ × ℤ => p.1)
    S2_cube_add_one_sq_sub_4_infinite ?_
  rintro x ⟨hx, k, rfl⟩
  have hodd : ¬ (2 ∣ ((2 * k) ^ 3 + 1) ^ 2 - 4) := by
    have h : ((2 * k) ^ 3 + 1) ^ 2 - 4 = 2 * (32 * k ^ 6 + 8 * k ^ 3 - 2) + 1 := by ring
    omega
  obtain ⟨A, B, hAB, hAodd, hBe⟩ := exists_sq_add_sq_odd_even hx.2 hodd
  obtain ⟨z, hz⟩ := hBe
  obtain ⟨y, hy⟩ : ∃ y : ℤ, A = (2 * k) ^ 3 + 2 * y + 1 := by
    obtain ⟨j, hj⟩ : ∃ j, A = 2 * j + 1 := by
      rcases Int.even_or_odd A with ⟨n, hn⟩ | ⟨n, hn⟩
      · exact absurd ⟨n, by omega⟩ hAodd
      · exact ⟨n, hn⟩
    exact ⟨j - 4 * k ^ 3, by rw [hj]; ring⟩
  refine ⟨(2 * k, y, z), ?_, rfl⟩
  simp only [mem_setOf_eq']
  have h4' : 4 * (y ^ 2 + (2 * k) ^ 3 * y + y + z ^ 2 + 1) = 0 := by
    rw [hy, hz] at hAB
    linear_combination -hAB
  linarith

end PolyQF

/-!
# Section 4: general binary quadratic forms

Let `F(y, z) = A y ^ 2 + B y z + C z ^ 2` be an integral binary quadratic form with
discriminant `Δ = B ^ 2 - 4 A C`. This file formalizes:

* the tangent-line construction and Proposition 4.1;
* Proposition 4.2 on the infinitude of solutions of the auxiliary equation (29);
* Proposition 4.4, solving the two equations (31);
* the description of degenerate forms (`Δ = 0`) at the end of Section 4, and the failure of
  multiplicativity for `2y^2 + yz + 2z^2`.
-/

namespace PolyQF

/-- The binary quadratic form `F(y, z) = A y ^ 2 + B y z + C z ^ 2`. -/
def BQF (A B C y z : ℤ) : ℤ := A * y ^ 2 + B * y * z + C * z ^ 2

/-- The discriminant `Δ = B ^ 2 - 4 A C` of `BQF A B C`. -/
def disc (A B C : ℤ) : ℤ := B ^ 2 - 4 * A * C

/-! ### The tangent-line identities (24)-(25) -/

/-- The first condition in (24): with `λ, μ` given by the parametrization (25), the linear
form `2Apλ + B(pμ + qλ) + 2Cqμ` equals `r`. -/
lemma tangent_line_eq {A B C m r v p q lam mu : ℤ} (hm : m = A * p ^ 2 + B * p * q + C * q ^ 2)
    (hm0 : m ≠ 0) (hlam : 2 * m * lam = r * p + v * (B * p + 2 * C * q))
    (hmu : 2 * m * mu = r * q - v * (2 * A * p + B * q)) :
    2 * A * p * lam + B * (p * mu + q * lam) + 2 * C * q * mu = r := by
  have h2m : (2 : ℤ) * m ≠ 0 := by simpa using hm0
  refine mul_left_cancel₀ h2m ?_
  linear_combination (2 * A * p + B * q) * hlam + (B * p + 2 * C * q) * hmu
    - (2 * r) * hm

/-- The second identity: `4 m F(λ, μ) = r ^ 2 - Δ v ^ 2`. -/
lemma tangent_conic_eq {A B C m r v p q lam mu : ℤ} (hm : m = A * p ^ 2 + B * p * q + C * q ^ 2)
    (hm0 : m ≠ 0) (hlam : 2 * m * lam = r * p + v * (B * p + 2 * C * q))
    (hmu : 2 * m * mu = r * q - v * (2 * A * p + B * q)) :
    4 * m * BQF A B C lam mu = r ^ 2 - disc A B C * v ^ 2 := by
  refine mul_left_cancel₀ hm0 ?_
  simp only [BQF, disc]
  linear_combination (A * (2 * m * lam + (r * p + v * (B * p + 2 * C * q)))
      + B * (r * q - v * (2 * A * p + B * q))) * hlam
    + (B * (2 * m * lam) + C * (2 * m * mu + (r * q - v * (2 * A * p + B * q)))) * hmu
    - (r ^ 2 - (B ^ 2 - 4 * A * C) * v ^ 2) * hm

/-- **The recovery formulas (28).** If `(x, v)` satisfies the auxiliary equation (26) and the
tangent-line coefficients `λ, μ` given by (25) are integral, then `y = p + sλ`, `z = q + sμ`
(with `s = Q(x) - u`) is an integral solution of `F(y, z) = R(Q(x))`. -/
lemma tangent_solution {A B C m r v p q lam mu s d : ℤ}
    (hm : m = A * p ^ 2 + B * p * q + C * q ^ 2) (hm0 : m ≠ 0)
    (hlam : 2 * m * lam = r * p + v * (B * p + 2 * C * q))
    (hmu : 2 * m * mu = r * q - v * (2 * A * p + B * q))
    (h26 : 4 * m * d - r ^ 2 = - disc A B C * v ^ 2) :
    BQF A B C (p + s * lam) (q + s * mu) = m + s * r + s ^ 2 * d := by
  have hline := tangent_line_eq hm hm0 hlam hmu
  have hconic := tangent_conic_eq hm hm0 hlam hmu
  have hd : BQF A B C lam mu = d := by
    refine mul_left_cancel₀ (a := 4 * m) (by simpa using hm0) ?_
    rw [hconic]
    linarith [h26]
  have hexp : BQF A B C (p + s * lam) (q + s * mu)
      = (A * p ^ 2 + B * p * q + C * q ^ 2)
        + s * (2 * A * p * lam + B * (p * mu + q * lam) + 2 * C * q * mu)
        + s ^ 2 * BQF A B C lam mu := by
    simp only [BQF]; ring
  rw [hexp, hline, hd, ← hm]

/-! ### Proposition 4.1 -/

/-- Divisibility by `2|m|` is the same as divisibility by `2m`. -/
lemma two_abs_dvd_iff {m N : ℤ} : 2 * |m| ∣ N ↔ 2 * m ∣ N := by
  rw [show (2 : ℤ) * |m| = |2 * m| by rw [abs_mul, abs_two], abs_dvd]

/-- For `Δ ≠ 0` and fixed `c`, only finitely many `v` satisfy `c = -Δ v ^ 2`. -/
lemma finite_setOf_neg_disc_sq {D c : ℤ} (hD : D ≠ 0) : {v : ℤ | c = -D * v ^ 2}.Finite := by
  rcases Set.eq_empty_or_nonempty {v : ℤ | c = -D * v ^ 2} with he | ⟨v₀, hv₀⟩
  · rw [he]; exact Set.finite_empty
  · refine ((Set.finite_singleton (-v₀)).insert v₀).subset ?_
    intro v hv
    simp only [mem_setOf_eq'] at hv hv₀
    have h1 : -D * v ^ 2 = -D * v₀ ^ 2 := by rw [← hv, ← hv₀]
    have h2 : v ^ 2 = v₀ ^ 2 := mul_left_cancel₀ (by simpa using hD) h1
    have h3 : (v - v₀) * (v + v₀) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl (by linarith)
    · refine Or.inr ?_
      simp only [Set.mem_singleton_iff]
      linarith

/-- **Proposition 4.1.** Assume `Δ = B^2 - 4AC ≠ 0`, that `m = R(u) = F(p, q) ≠ 0`, and let
`Dᵤ` be defined by (6), `r = R'(u)`. If there are infinitely many integer pairs `(x, v)`
satisfying the auxiliary equation (26) and the congruences (27), then the equation
`F(y, z) = R(Q(x))` is solvable in integers `(y, z)` for infinitely many integers `x`. -/
theorem prop_4_1 {A B C : ℤ} {R Q Du : Polynomial ℤ} {u p q : ℤ}
    (hD : disc A B C ≠ 0)
    (hDu : R = Polynomial.C (R.eval u)
      + Polynomial.C (R.derivative.eval u) * (Polynomial.X - Polynomial.C u)
      + (Polynomial.X - Polynomial.C u) ^ 2 * Du)
    (hm : R.eval u = BQF A B C p q) (hm0 : R.eval u ≠ 0)
    (hinf : {w : ℤ × ℤ |
        4 * R.eval u * Du.eval (Q.eval w.1) - R.derivative.eval u ^ 2
            = - disc A B C * w.2 ^ 2 ∧
        2 * |R.eval u| ∣ R.derivative.eval u * p + w.2 * (B * p + 2 * C * q) ∧
        2 * |R.eval u| ∣ R.derivative.eval u * q - w.2 * (2 * A * p + B * q)}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, BQF A B C y z = R.eval (Q.eval x)}.Infinite := by
  have hfib : ∀ x : ℤ, {v : ℤ |
      4 * R.eval u * Du.eval (Q.eval x) - R.derivative.eval u ^ 2 = - disc A B C * v ^ 2 ∧
      2 * |R.eval u| ∣ R.derivative.eval u * p + v * (B * p + 2 * C * q) ∧
      2 * |R.eval u| ∣ R.derivative.eval u * q - v * (2 * A * p + B * q)}.Finite := by
    intro x
    refine (finite_setOf_neg_disc_sq (c := 4 * R.eval u * Du.eval (Q.eval x)
      - R.derivative.eval u ^ 2) hD).subset ?_
    rintro v ⟨h1, -, -⟩
    exact h1
  have hx := infinite_fst_of_infinite hinf hfib
  refine hx.mono ?_
  rintro x ⟨v, h26, h27a, h27b⟩
  have habs : (2 : ℤ) * |R.eval u| = |2 * R.eval u| := by
    rw [abs_mul, abs_two]
  rw [habs, abs_dvd] at h27a h27b
  obtain ⟨lam, hlam⟩ := h27a
  obtain ⟨mu, hmu⟩ := h27b
  refine ⟨p + (Q.eval x - u) * lam, q + (Q.eval x - u) * mu, ?_⟩
  have hsol := tangent_solution (A := A) (B := B) (C := C) (m := R.eval u)
    (r := R.derivative.eval u) (v := v) (p := p) (q := q) (lam := lam) (mu := mu)
    (s := Q.eval x - u) (d := Du.eval (Q.eval x)) hm hm0 hlam.symm hmu.symm h26
  rw [hsol, eval_taylorQuot hDu (Q.eval x)]
  ring

/-! ### Proposition 4.2 -/

/-- If `a` is not a perfect square, neither is `4 a`. -/
lemma not_isSquare_four_mul {a : ℤ} (ha : ¬ IsSquare a) : ¬ IsSquare (4 * a) := by
  have h := not_isSquare_mul_sq (A := a) (N := 2) ha (by norm_num)
  intro hcon
  exact h (by rwa [show (a : ℤ) * 2 ^ 2 = 4 * a by ring])

/-- **Proposition 4.2.** Assume (a) either `a = 0` or `-aΔ` is a positive non-square,
(b) `b^2 - 4ac ≠ 0`, and (c) the equation `a x^2 + b x + c = -Δ v^2` has an integer solution
`(x₀, v₀)`. Then it has infinitely many integer solutions `(x, v)` with `v ≡ v₀ (mod 2m)`;
in particular, if `v₀` satisfies the congruences (27), then so do all these `v`. -/
theorem prop_4_2 {a b c D m : ℤ} (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < -a * D ∧ ¬ IsSquare (-a * D))) (hb : b ^ 2 - 4 * a * c ≠ 0)
    {x₀ v₀ : ℤ} (hsol : a * x₀ ^ 2 + b * x₀ + c = -D * v₀ ^ 2) :
    {w : ℤ × ℤ | a * w.1 ^ 2 + b * w.1 + c = -D * w.2 ^ 2 ∧ 2 * m ∣ w.2 - v₀}.Infinite := by
  rcases ha with rfl | ⟨hpos, hsq⟩
  · -- the linear case
    have hb0 : b ≠ 0 := by
      intro h; apply hb; rw [h]; ring
    have hsol0 : b * x₀ + c = -D * v₀ ^ 2 := by linear_combination hsol
    set g : ℤ → ℤ × ℤ :=
      fun k => (x₀ - D * (4 * m * k * v₀ + 4 * m ^ 2 * b * k ^ 2), v₀ + 2 * m * b * k) with hg
    have hginj : Function.Injective g := by
      intro k k' hkk
      have h2 : v₀ + 2 * m * b * k = v₀ + 2 * m * b * k' := congrArg Prod.snd hkk
      have h3 : 2 * m * b * (k - k') = 0 := by linarith
      have hmb : 2 * m * b ≠ 0 := by
        simp only [ne_eq, mul_eq_zero]
        push Not
        exact ⟨by simpa using hm, hb0⟩
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hmb
      · linarith
    refine ((Set.infinite_univ (α := ℤ)).image
      (Set.injOn_of_injective hginj)).mono ?_
    rintro _ ⟨k, -, rfl⟩
    refine ⟨?_, ⟨b * k, by simp only [hg]; ring⟩⟩
    simp only [hg]
    linear_combination hsol0
  · -- the genuinely quadratic case
    have ha0 : a ≠ 0 := by
      intro h; rw [h] at hpos; simp at hpos
    have hA : (0 : ℤ) < 4 * (-a * D) := by linarith
    have hAsq : ¬ IsSquare (4 * (-a * D)) := not_isSquare_four_mul hsq
    have hN : (2 * a * (2 * m) : ℤ) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero]
      push Not
      refine ⟨⟨by norm_num, ha0⟩, by simpa using hm⟩
    have hX₀ : (2 * a * x₀ + b) ^ 2 - 4 * (-a * D) * v₀ ^ 2 = b ^ 2 - 4 * a * c := by
      linear_combination (4 * a) * hsol
    have hpell := pell_solutions_infinite hA hAsq hb hN hX₀
    refine infinite_of_subset_image (fun w : ℤ × ℤ => 2 * a * w.1 + b) hpell ?_
    rintro X ⟨V, hXV, hXc, hVc⟩
    obtain ⟨k, hk⟩ := hXc
    have hdvd : 2 * a ∣ X - b := ⟨2 * m * k + x₀, by linarith⟩
    have e1 : 2 * a * ((X - b) / (2 * a)) = X - b :=
      Int.mul_ediv_cancel' hdvd
    refine ⟨((X - b) / (2 * a), V), ⟨?_, ?_⟩, ?_⟩
    · show a * ((X - b) / (2 * a)) ^ 2 + b * ((X - b) / (2 * a)) + c = -D * V ^ 2
      set x : ℤ := (X - b) / (2 * a) with hxdef
      have hX : X = 2 * a * x + b := by linarith
      rw [hX] at hXV
      have h4 : (4 * a) * (a * x ^ 2 + b * x + c - (-D * V ^ 2)) = 0 := by
        linear_combination hXV
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h (by simpa using ha0)
      · linarith
    · show 2 * m ∣ V - v₀
      obtain ⟨l, hl⟩ := hVc
      exact ⟨2 * a * l, by linear_combination hl⟩
    · show 2 * a * ((X - b) / (2 * a)) + b = X
      linarith

/-- The congruences (27) only depend on `v` modulo `2|m|`: if `v₀` satisfies them and
`v ≡ v₀ (mod 2m)`, then so does `v`. This is what links Proposition 4.2 to Proposition 4.1. -/
lemma congr_27_of_congr {A B C m r p q v v₀ : ℤ} (hv : 2 * m ∣ v - v₀)
    (h₀a : 2 * |m| ∣ r * p + v₀ * (B * p + 2 * C * q))
    (h₀b : 2 * |m| ∣ r * q - v₀ * (2 * A * p + B * q)) :
    2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧
      2 * |m| ∣ r * q - v * (2 * A * p + B * q) := by
  rw [two_abs_dvd_iff] at h₀a h₀b
  obtain ⟨k, hk⟩ := hv
  obtain ⟨s, hs⟩ := h₀a
  obtain ⟨t, ht⟩ := h₀b
  refine ⟨two_abs_dvd_iff.mpr ⟨s + k * (B * p + 2 * C * q), ?_⟩,
    two_abs_dvd_iff.mpr ⟨t - k * (2 * A * p + B * q), ?_⟩⟩
  · linear_combination hs + (B * p + 2 * C * q) * hk
  · linear_combination ht - (2 * A * p + B * q) * hk

/-! ### Proposition 4.4 -/

/-- **Proposition 4.4 (a).** `2 y ^ 2 + y z + 2 z ^ 2 = x ^ 3 + 1` has infinitely many integer
solutions, given by the explicit family of the paper. -/
theorem prop_4_4_a :
    {w : ℤ × ℤ × ℤ | BQF 2 1 2 w.2.1 w.2.2 = w.1 ^ 3 + 1}.Infinite := by
  refine infinite_of_subset_image (fun w : ℤ × ℤ × ℤ => w.1)
    (T := (fun n : ℤ => 30 * n ^ 2 + 15 * n + 1) '' Set.Ici 0) ?_ ?_
  · refine (Set.Ici_infinite (0 : ℤ)).image ?_
    intro n hn n' hn' h
    simp only [Set.mem_Ici] at hn hn'
    simp only at h
    nlinarith
  · rintro _ ⟨n, -, rfl⟩
    refine ⟨(30 * n ^ 2 + 15 * n + 1, 30 * n ^ 3 + 45 * n ^ 2 + 15 * n + 1,
      -120 * n ^ 3 - 90 * n ^ 2 - 15 * n), ?_, rfl⟩
    simp only [mem_setOf_eq', BQF]
    ring

/-- **Proposition 4.4 (b).** `2 y ^ 2 + y z + 2 z ^ 2 = x ^ 3 - 1` has infinitely many integer
solutions, given by the explicit family of the paper. -/
theorem prop_4_4_b :
    {w : ℤ × ℤ × ℤ | BQF 2 1 2 w.2.1 w.2.2 = w.1 ^ 3 - 1}.Infinite := by
  refine infinite_of_subset_image (fun w : ℤ × ℤ × ℤ => w.1)
    (T := (fun n : ℤ => 570 * n ^ 2 + 225 * n + 24) '' Set.Ici 0) ?_ ?_
  · refine (Set.Ici_infinite (0 : ℤ)).image ?_
    intro n hn n' hn' h
    simp only [Set.mem_Ici] at hn hn'
    simp only at h
    nlinarith
  · rintro _ ⟨n, -, rfl⟩
    refine ⟨(570 * n ^ 2 + 225 * n + 24, 9690 * n ^ 3 + 6105 * n ^ 2 + 1189 * n + 71,
      -4560 * n ^ 3 - 1230 * n ^ 2 + 89 * n + 29), ?_, rfl⟩
    simp only [mem_setOf_eq', BQF]
    ring

/-! ### Non-multiplicativity of `2y^2 + yz + 2z^2` -/

/-- The form `2y^2 + yz + 2z^2` represents `2`. -/
theorem BQF_two_one_two_represents_two : BQF 2 1 2 0 1 = 2 := by
  simp [BQF]

/-- The form `2y^2 + yz + 2z^2` does not represent `4`; hence it is not multiplicative. -/
theorem BQF_two_one_two_not_represents_four : ¬ ∃ y z : ℤ, BQF 2 1 2 y z = 4 := by
  rintro ⟨y, z, h⟩
  have h3 : ∀ a b : ZMod 3, 2 * a ^ 2 + a * b + 2 * b ^ 2 ≠ 4 := by decide
  refine h3 (y : ZMod 3) (z : ZMod 3) ?_
  have := congrArg (fun n : ℤ => (n : ZMod 3)) h
  simpa [BQF] using this

/-! ### Comparison with Section 2 -/

/-- For the form `y ^ 2 + z ^ 2` we have `Δ = -4`. -/
lemma disc_sum_two_squares : disc 1 0 1 = -4 := by
  simp [disc]

/-- For `Δ = -4`, any integer solution `V` of the auxiliary equation (8) is even, so that (8)
reduces to (26) after writing `V = 2v`. -/
lemma even_of_aux_eight {m d r V : ℤ} (h : 4 * m * d - r ^ 2 = V ^ 2) : (2 : ℤ) ∣ V := by
  have h4 : (4 : ℤ) ∣ V ^ 2 + r ^ 2 := ⟨m * d, by linarith⟩
  obtain ⟨A', B', hAB, hA', -⟩ :=
    exists_sq_add_sq_both_even (n := V ^ 2 + r ^ 2) ⟨V, r, rfl⟩ h4
  -- the parity of `V` is determined by the equation itself
  rcases Int.even_or_odd V with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j, by omega⟩
  · exfalso
    obtain ⟨k, hk⟩ := h4
    have hV : V ^ 2 = 4 * (j ^ 2 + j) + 1 := by rw [hj]; ring
    obtain ⟨l, hl⟩ := sq_mod_four r
    rcases hl with hl | hl <;> omega

/-- The form `4(y^2 + z^2)` represents `4` but not `1`: multiplicativity alone does not allow
cancellation, which is why property (*) is needed in Section 2. -/
theorem four_mul_sum_two_squares_not_represents_one :
    (∃ y z : ℤ, 4 * (y ^ 2 + z ^ 2) = 4) ∧ ¬ ∃ y z : ℤ, 4 * (y ^ 2 + z ^ 2) = 1 := by
  refine ⟨⟨1, 0, by norm_num⟩, ?_⟩
  rintro ⟨y, z, h⟩
  omega

/-! ### The degenerate case `Δ = 0` -/

/-- If the discriminant vanishes, then `(A, B, C) = (k n ^ 2, 2 k n m, k m ^ 2)` for some
integers `k, n, m`. -/
theorem degenerate_disc_zero {A B C : ℤ} (h : disc A B C = 0) :
    ∃ k n m : ℤ, A = k * n ^ 2 ∧ B = 2 * k * n * m ∧ C = k * m ^ 2 := by
  simp only [disc] at h
  by_cases hA : A = 0
  · subst hA
    have hB : B = 0 := by
      have : B ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact ⟨C, 0, 1, by simp, by simp [hB], by simp⟩
  · -- `B` is even
    obtain ⟨B', rfl⟩ : ∃ B', B = 2 * B' := by
      rcases Int.even_or_odd B with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j, by omega⟩
      · exfalso
        have h1 : B ^ 2 = 4 * (j ^ 2 + j) + 1 := by rw [hj]; ring
        have h2 : (4 : ℤ) * (A * C) = 4 * (j ^ 2 + j) + 1 := by linarith
        omega
    have hAC : B' ^ 2 = A * C := by linarith
    have hgpos : 0 < Int.gcd A B' := Int.gcd_pos_of_ne_zero_left B' hA
    set d : ℤ := (Int.gcd A B' : ℤ) with hd
    have hd0 : d ≠ 0 := Int.natCast_ne_zero.mpr hgpos.ne'
    have hdvdA : d ∣ A := Int.gcd_dvd_left A B'
    have hdvdB : d ∣ B' := Int.gcd_dvd_right A B'
    set alpha : ℤ := A / d with halpha
    set beta : ℤ := B' / d with hbeta
    have hal : A = d * alpha := (Int.mul_ediv_cancel' hdvdA).symm
    have hbe : B' = d * beta := (Int.mul_ediv_cancel' hdvdB).symm
    have hcop : IsCoprime alpha beta := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact Int.gcd_div_gcd_div_gcd hgpos
    have key : d * beta ^ 2 = alpha * C := by
      refine mul_left_cancel₀ hd0 ?_
      have h1 : (d * beta) ^ 2 = (d * alpha) * C := by rw [← hbe, ← hal]; exact hAC
      linear_combination h1
    have hdvd : alpha ∣ d := by
      have h1 : alpha ∣ d * beta ^ 2 := ⟨C, key⟩
      exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right h1
    obtain ⟨k, hk⟩ := hdvd
    have halne : alpha ≠ 0 := by
      intro h0
      exact hA (by rw [hal, h0, mul_zero])
    refine ⟨k, alpha, beta, ?_, ?_, ?_⟩
    · rw [hal, hk]; ring
    · rw [hbe, hk]; ring
    · refine mul_left_cancel₀ halne ?_
      rw [← key, hk]; ring
  
/-- A degenerate form is `k` times the square of a linear form. -/
theorem degenerate_form_eq {k n m y z : ℤ} :
    BQF (k * n ^ 2) (2 * k * n * m) (k * m ^ 2) y z = k * (n * y + m * z) ^ 2 := by
  simp only [BQF]; ring

end PolyQF

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
# On the polynomial values represented by quadratic forms — main results

This section collects the main results of the paper *On the polynomial values represented by
quadratic forms* by B. Grechuk and J. Agbanwa, as formalized above:

* the set `S₂` and property `(*)` of Section 2;
* the Pell-type engine behind Propositions 2.3 and 4.2;
* elementary parity and non-square tools;
* identities (6) and (7), Propositions 2.2 and 2.3;
* Algorithm 2.4 specialised to `R(t) = t³ + f`, and Corollaries 3.1 and 3.2;
* Section 4 on general binary quadratic forms.
-/

namespace PolyQF.Main

open PolyQF

/-! ## Section 2 -/

/-- **Property (*)** (Section 2): for positive integers `a, b`, if `S₂` contains two of the
integers `a`, `b`, `ab`, then it contains all three of them. -/
theorem property_star {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    (S2 a → S2 b → S2 (a * b)) ∧ (S2 a → S2 (a * b) → S2 b) ∧ (S2 b → S2 (a * b) → S2 a) :=
  S2_star ha hb

/-- **Identity (6)**: existence and uniqueness of the polynomial `Dᵤ`. -/
theorem identity_six (R : Polynomial ℤ) (u : ℤ) :
    ∃! D : Polynomial ℤ, R = Polynomial.C (R.eval u)
      + Polynomial.C (R.derivative.eval u) * (Polynomial.X - Polynomial.C u)
      + (Polynomial.X - Polynomial.C u) ^ 2 * D :=
  exists_unique_taylorQuot R u

/-- **Proposition 2.2.** -/
theorem proposition_2_2 {R Q : Polynomial ℤ} (hR : 0 < R.natDegree) (hQ : 0 < Q.natDegree)
    {u : ℤ} (hRu : S2 (R.eval u)) {Du : Polynomial ℤ}
    (hDu : R = Polynomial.C (R.eval u)
      + Polynomial.C (R.derivative.eval u) * (Polynomial.X - Polynomial.C u)
      + (Polynomial.X - Polynomial.C u) ^ 2 * Du)
    (hinf : {p : ℤ × ℤ |
      4 * R.eval u * Du.eval (Q.eval p.1) - R.derivative.eval u ^ 2 = p.2 ^ 2}.Infinite) :
    {x : ℤ | S2 (R.eval (Q.eval x))}.Infinite :=
  prop_2_2 hR hQ hRu hDu hinf

/-- **Proposition 2.3.** -/
theorem proposition_2_3 {a b c : ℤ} (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a))
    (hb : b ^ 2 - 4 * a * c ≠ 0) {x₀ v₀ : ℤ} (hsol : a * x₀ ^ 2 + b * x₀ + c = v₀ ^ 2) :
    {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite :=
  prop_2_3 ha hb hsol

/-! ## Section 3 -/

/-- `x ^ 6 - 4` is a sum of two squares for infinitely many integers `x`. -/
theorem x_pow_six_sub_four_sum_two_squares : {x : ℤ | S2 (x ^ 6 - 4)}.Infinite :=
  S2_x6_sub_4_infinite

/-- **Corollary 3.1.** Equation (2), `y² + x³y + z² + 1 = 0`, has infinitely many integer
solutions. -/
theorem equation_2_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite :=
  cor_3_1

/-- **Corollary 3.2**, equation (13): `y² + x³y + z² - 2 = 0`. -/
theorem equation_13_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite :=
  cor_3_2_eq13

/-- **Corollary 3.2**, equation (14): `y² + x³y + z² + z - 1 = 0`. -/
theorem equation_14_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite :=
  cor_3_2_eq14

/-- **Corollary 3.2**, equation (15): `y² + x³y + z² + z + 1 = 0`. -/
theorem equation_15_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite :=
  cor_3_2_eq15

/-- **Corollary 3.2**, equation (16): `y² + x³y + y + z² + 1 = 0`. -/
theorem equation_16_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite :=
  cor_3_2_eq16

/-! ## Section 4 -/

/-- **Proposition 4.1.** -/
theorem proposition_4_1 {A B C : ℤ} {R Q Du : Polynomial ℤ} {u p q : ℤ}
    (hD : disc A B C ≠ 0)
    (hDu : R = Polynomial.C (R.eval u)
      + Polynomial.C (R.derivative.eval u) * (Polynomial.X - Polynomial.C u)
      + (Polynomial.X - Polynomial.C u) ^ 2 * Du)
    (hm : R.eval u = BQF A B C p q) (hm0 : R.eval u ≠ 0)
    (hinf : {w : ℤ × ℤ |
        4 * R.eval u * Du.eval (Q.eval w.1) - R.derivative.eval u ^ 2
            = - disc A B C * w.2 ^ 2 ∧
        2 * |R.eval u| ∣ R.derivative.eval u * p + w.2 * (B * p + 2 * C * q) ∧
        2 * |R.eval u| ∣ R.derivative.eval u * q - w.2 * (2 * A * p + B * q)}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, BQF A B C y z = R.eval (Q.eval x)}.Infinite :=
  prop_4_1 hD hDu hm hm0 hinf

/-- **Proposition 4.2.** -/
theorem proposition_4_2 {a b c D m : ℤ} (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < -a * D ∧ ¬ IsSquare (-a * D))) (hb : b ^ 2 - 4 * a * c ≠ 0)
    {x₀ v₀ : ℤ} (hsol : a * x₀ ^ 2 + b * x₀ + c = -D * v₀ ^ 2) :
    {w : ℤ × ℤ | a * w.1 ^ 2 + b * w.1 + c = -D * w.2 ^ 2 ∧ 2 * m ∣ w.2 - v₀}.Infinite :=
  prop_4_2 hm ha hb hsol

/-- **Proposition 4.4 (a).** `2y² + yz + 2z² = x³ + 1` has infinitely many integer
solutions. -/
theorem equation_31a_infinite :
    {w : ℤ × ℤ × ℤ | BQF 2 1 2 w.2.1 w.2.2 = w.1 ^ 3 + 1}.Infinite :=
  prop_4_4_a

/-- **Proposition 4.4 (b).** `2y² + yz + 2z² = x³ - 1` has infinitely many integer
solutions. -/
theorem equation_31b_infinite :
    {w : ℤ × ℤ × ℤ | BQF 2 1 2 w.2.1 w.2.2 = w.1 ^ 3 - 1}.Infinite :=
  prop_4_4_b

/-- The form `2y² + yz + 2z²` is not multiplicative: it represents `2` but not `2 * 2 = 4`. -/
theorem form_2_1_2_not_multiplicative :
    BQF 2 1 2 0 1 = 2 ∧ ¬ ∃ y z : ℤ, BQF 2 1 2 y z = 4 :=
  ⟨BQF_two_one_two_represents_two, BQF_two_one_two_not_represents_four⟩

/-- The degenerate case `Δ = 0`: the form is `k` times the square of a linear form. -/
theorem degenerate_case {A B C : ℤ} (h : disc A B C = 0) :
    ∃ k n m : ℤ, A = k * n ^ 2 ∧ B = 2 * k * n * m ∧ C = k * m ^ 2 ∧
      ∀ y z : ℤ, BQF A B C y z = k * (n * y + m * z) ^ 2 := by
  obtain ⟨k, n, m, hA, hB, hC⟩ := degenerate_disc_zero h
  refine ⟨k, n, m, hA, hB, hC, fun y z => ?_⟩
  subst hA; subst hB; subst hC
  exact degenerate_form_eq

end PolyQF.Main

/-!
# Challenge statements

Self-contained statements of the main results of the paper *On the polynomial values
represented by quadratic forms* (B. Grechuk, J. Agbanwa).  Each statement below is phrased
using only `Mathlib` notions, so that it can be read independently of the development above.
The statements are discharged in the `Solution` namespace below.
-/

namespace Challenge

/-- `IsSumTwoSquares n`: the positive integer `n` lies in the set `S₂` of sums of two integer
squares. -/
def IsSumTwoSquares (n : ℤ) : Prop := 0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2

/-- Property `(*)` of Section 2: for positive `a, b`, membership of two of `a`, `b`, `ab` in
`S₂` implies membership of the third. -/
def PropertyStar : Prop :=
  ∀ a b : ℤ, 0 < a → 0 < b →
    (IsSumTwoSquares a → IsSumTwoSquares b → IsSumTwoSquares (a * b)) ∧
    (IsSumTwoSquares a → IsSumTwoSquares (a * b) → IsSumTwoSquares b) ∧
    (IsSumTwoSquares b → IsSumTwoSquares (a * b) → IsSumTwoSquares a)

/-- Proposition 2.3: the equation `a x² + b x + c = v²` has infinitely many integer
solutions `x` under conditions (a), (b), (c). -/
def Proposition23 : Prop :=
  ∀ a b c x₀ v₀ : ℤ, (a = 0 ∨ (0 < a ∧ ¬ IsSquare a)) → b ^ 2 - 4 * a * c ≠ 0 →
    a * x₀ ^ 2 + b * x₀ + c = v₀ ^ 2 →
    {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite

/-- The key arithmetic statement of Section 3: `x⁶ - 4` is a sum of two squares for
infinitely many integers `x`. -/
def SumTwoSquaresSixthPower : Prop :=
  {x : ℤ | IsSumTwoSquares (x ^ 6 - 4)}.Infinite

/-- Corollary 3.1: equation (2), `y² + x³y + z² + 1 = 0`. -/
def Equation2 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite

/-- Corollary 3.2, equation (13): `y² + x³y + z² - 2 = 0`. -/
def Equation13 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 - 2 = 0}.Infinite

/-- Corollary 3.2, equation (14): `y² + x³y + z² + z - 1 = 0`. -/
def Equation14 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 - 1 = 0}.Infinite

/-- Corollary 3.2, equation (15): `y² + x³y + z² + z + 1 = 0`. -/
def Equation15 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.2 ^ 2 + p.2.2 + 1 = 0}.Infinite

/-- Corollary 3.2, equation (16): `y² + x³y + y + z² + 1 = 0`. -/
def Equation16 : Prop :=
  {p : ℤ × ℤ × ℤ | p.2.1 ^ 2 + p.1 ^ 3 * p.2.1 + p.2.1 + p.2.2 ^ 2 + 1 = 0}.Infinite

/-- Proposition 4.4 (a): `2y² + yz + 2z² = x³ + 1`. -/
def Equation31a : Prop :=
  {w : ℤ × ℤ × ℤ | 2 * w.2.1 ^ 2 + w.2.1 * w.2.2 + 2 * w.2.2 ^ 2 = w.1 ^ 3 + 1}.Infinite

/-- Proposition 4.4 (b): `2y² + yz + 2z² = x³ - 1`. -/
def Equation31b : Prop :=
  {w : ℤ × ℤ × ℤ | 2 * w.2.1 ^ 2 + w.2.1 * w.2.2 + 2 * w.2.2 ^ 2 = w.1 ^ 3 - 1}.Infinite

/-- The form `2y² + yz + 2z²` is not multiplicative: it represents `2` but not `4`. -/
def FormNotMultiplicative : Prop :=
  (∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 2) ∧
    ¬ ∃ y z : ℤ, 2 * y ^ 2 + y * z + 2 * z ^ 2 = 4

/-- The degenerate case `Δ = 0` of Section 4. -/
def DegenerateForms : Prop :=
  ∀ A B C : ℤ, B ^ 2 - 4 * A * C = 0 →
    ∃ k n m : ℤ, A = k * n ^ 2 ∧ B = 2 * k * n * m ∧ C = k * m ^ 2 ∧
      ∀ y z : ℤ, A * y ^ 2 + B * y * z + C * z ^ 2 = k * (n * y + m * z) ^ 2

end Challenge

/-!
# Solutions to the challenge statements

Every statement of the `Challenge` namespace is discharged here from the development above.
-/

namespace Solution

open PolyQF

/-- The two notions of "sum of two squares" agree. -/
lemma isSumTwoSquares_iff (n : ℤ) : Challenge.IsSumTwoSquares n ↔ S2 n := Iff.rfl

theorem property_star : Challenge.PropertyStar := fun _ _ ha hb => S2_star ha hb

theorem proposition_23 : Challenge.Proposition23 :=
  fun _ _ _ _ _ ha hb hsol => prop_2_3 ha hb hsol

theorem sumTwoSquaresSixthPower : Challenge.SumTwoSquaresSixthPower := S2_x6_sub_4_infinite

theorem equation2 : Challenge.Equation2 := cor_3_1

theorem equation13 : Challenge.Equation13 := cor_3_2_eq13

theorem equation14 : Challenge.Equation14 := cor_3_2_eq14

theorem equation15 : Challenge.Equation15 := cor_3_2_eq15

theorem equation16 : Challenge.Equation16 := cor_3_2_eq16

theorem equation31a : Challenge.Equation31a := by
  have h := prop_4_4_a
  refine h.mono ?_
  rintro w hw
  simpa [BQF] using hw

theorem equation31b : Challenge.Equation31b := by
  have h := prop_4_4_b
  refine h.mono ?_
  rintro w hw
  simpa [BQF] using hw

theorem formNotMultiplicative : Challenge.FormNotMultiplicative := by
  refine ⟨⟨0, 1, by norm_num⟩, ?_⟩
  rintro ⟨y, z, h⟩
  exact BQF_two_one_two_not_represents_four ⟨y, z, by simpa [BQF] using h⟩

theorem degenerateForms : Challenge.DegenerateForms := by
  intro A B C h
  obtain ⟨k, n, m, hA, hB, hC, hform⟩ := PolyQF.Main.degenerate_case (A := A) (B := B) (C := C)
    (by simpa [disc] using h)
  refine ⟨k, n, m, hA, hB, hC, fun y z => ?_⟩
  simpa [BQF] using hform y z

end Solution
