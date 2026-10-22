import Mathlib

-- File revision 3 (2026-10-21): uses no `eval_finset_sum`, `Set.mem_setOf_eq`,
-- `Polynomial.finite_setOf_isRoot`, `Set.Infinite.diff`, `push_neg` or `haveI`.

/-!
# On the polynomial values represented by binary quadratic forms

A Lean formalisation of the paper *"On the polynomial values represented by binary
quadratic forms"* by B. Grechuk and J. Agbanwa (revision R1).

The whole mathematical development lives in this single file.  It is self-contained:
every definition needed to read the statements (`PolyQF.S2`, `PolyQF.Du`, `PolyQF.bqf`,
`PolyQF.AdmissibleDegrees`) is introduced in this file. The principal results listed
below are stated as theorems and proved here, with no proof placeholders or extra axioms.
The algorithm theorems establish correctness when their seed hypotheses are satisfied;
they do not implement the full search or assert termination for arbitrary inputs.

Comparator setup (in the project root): `Challenge.lean` restates the main results with
`sorry` proofs (namespace `Paper`, with the four definitions above copied verbatim),
`Solution.lean` proves each of them by the corresponding theorem of this file, and
`comparator.json` lists the theorems to be compared and the permitted axioms.

Numbering follows the paper (R1):

* §2: property (*), Proposition 2.1, Proposition 2.2, Algorithm 2.1
  (correctness of its output, the fact that Step 2 always produces an equation of the
  form `a x² + b x + c = v²`, and the finite seed test in the linear case `a = 0`);
* §3: Corollary 3.1 (`y² + x³y + z² + 1 = 0` has infinitely many integer solutions),
  Corollary 3.2 (the four equations (13)–(16)), and the closing remark on
  `y² + z² = x⁶ + 3`;
* §4: Proposition 4.1 (including the explicit recovery formulas (28)),
  Proposition 4.2, Algorithm 4.1 (correctness, Step 2, linear seed test),
  Proposition 4.3 (both equations (31), with the explicit families),
  the non-multiplicativity example, the degenerate case `Δ = 0`
  (parametrisation and the "if and only if" criterion), and the comparison with §2.

Not formalised: the informal discussion of Section 1 (lengths of equations, the list of
open equations in Table 1) and the claim in the footnote to Corollary 3.1 that `u = 50` is
the smallest positive seed satisfying all conditions of Algorithm 2.1 for `f = -4` (the
proof uses `u = 162`, which is fully checked here).

Sets of integer solutions of equations in variables `(x, y, z)` are sets of triples
`s : ℤ × ℤ × ℤ` with `s = (x, y, z)`, i.e. `x = s.1`, `y = s.2.1`, `z = s.2.2`.

Regarding citations: the paper invokes [11, Proposition 5.4] (the monograph
*Polynomial Diophantine equations — a systematic approach*) in the proof of
Proposition 2.2, and Gauss's theorem [11, Proposition 3.14] in the proof of
Proposition 4.2.  Neither result is assumed here: both are replaced by a self-contained
Pell-equation argument (`PolyQF.pell_orbit_infinite`) proved below from Mathlib's
existence theorem for nontrivial solutions of Pell's equation.
-/

open Polynomial

namespace PolyQF

/-! ## Basic definitions -/

/-- `𝒮₂`: the set of *positive* integers that are sums of two integer squares. -/
def S2 : Set ℤ := {n | 0 < n ∧ ∃ y z : ℤ, n = y ^ 2 + z ^ 2}

/-- The polynomial `D_u(t)` of equation (6): the unique integer polynomial with
`R(t) = R(u) + R'(u)(t-u) + (t-u)² D_u(t)`
(see `taylor_identity` and `Du_unique`).  It is defined through the Taylor expansion
of `R` at `u`: `D_u(t) = ∑_{k ≥ 0} c_{k+2} (t-u)^k` where `R(t) = ∑ c_k (t-u)^k`. -/
noncomputable def Du (R : ℤ[X]) (u : ℤ) : ℤ[X] :=
  ∑ k ∈ Finset.range (R.natDegree + 1), C ((taylor u R).coeff (k + 2)) * (X - C u) ^ k

/-- The integral binary quadratic form `F(y,z) = A y² + B y z + C z²` of (19). -/
def bqf (A B C y z : ℤ) : ℤ := A * y ^ 2 + B * y * z + C * z ^ 2


/-! ## The Taylor identity (6) and the tangent identity (7) -/

/-- Membership in a set-builder set (stated locally so the file does not depend on the
name of the corresponding Mathlib lemma, which differs between Mathlib versions). -/
@[simp] lemma mem_setOf_iff' {α : Type*} (p : α → Prop) (a : α) : a ∈ {x | p x} ↔ p a :=
  Iff.rfl

/-- Evaluation of a finite sum of polynomials (stated locally so the file does not depend on
the name of the corresponding Mathlib lemma, which differs between Mathlib versions). -/
lemma eval_sum' {ι : Type*} (s : Finset ι) (g : ι → ℤ[X]) (t : ℤ) :
    (∑ i ∈ s, g i).eval t = ∑ i ∈ s, (g i).eval t :=
  map_sum (evalRingHom t) g s

/-- The integer roots of a nonzero integer polynomial form a finite set. -/
lemma finite_setOf_isRoot' {p : ℤ[X]} (hp : p ≠ 0) : {x : ℤ | p.IsRoot x}.Finite :=
  p.roots.toFinset.finite_toSet.subset fun x hx => by
    simpa [Multiset.mem_toFinset, mem_roots hp] using hx

/-- Equation (6): `R(t) = R(u) + R'(u)(t-u) + (t-u)² D_u(t)`. -/
theorem taylor_identity (R : ℤ[X]) (u t : ℤ) :
    R.eval t = R.eval u + R.derivative.eval u * (t - u) + (t - u) ^ 2 * (Du R u).eval t := by
  have h1 : R.eval t = (taylor u R).eval (t - u) := by rw [taylor_eval]; ring_nf
  rw [h1, eval_eq_sum_range' (n := R.natDegree + 3) (by rw [natDegree_taylor]; omega)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Du, eval_sum', eval_mul, eval_C, eval_pow, eval_sub, eval_X, Finset.mul_sum,
    taylor_coeff_zero, zero_add, taylor_coeff_one]
  rw [add_assoc, add_comm]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro k _; ring

/-- Uniqueness of `D_u`: any integer polynomial satisfying the Taylor identity (6) for all
integers `t` is equal to `Du R u`. -/
theorem Du_unique (R D : ℤ[X]) (u : ℤ)
    (hD : ∀ t, R.eval t = R.eval u + R.derivative.eval u * (t - u) + (t - u) ^ 2 * D.eval t) :
    D = Du R u := by
  apply eq_of_infinite_eval_eq
  apply ((Set.finite_singleton u).infinite_compl).mono
  intro t ht
  have h1 := hD t
  have h2 := taylor_identity R u t
  have hne : (t - u) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht)
  exact mul_left_cancel₀ hne (by linarith)

/-- `deg D_u ≤ deg R - 2`. -/
theorem natDegree_Du_le (R : ℤ[X]) (u : ℤ) : (Du R u).natDegree ≤ R.natDegree - 2 := by
  unfold Du
  apply natDegree_sum_le_of_forall_le
  intro k _
  by_cases hk : k ≤ R.natDegree - 2
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_pow_le).trans ?_
    rw [natDegree_X_sub_C u]; omega
  · have : (taylor u R).coeff (k + 2) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; rw [natDegree_taylor]; omega
    simp [this]

/-- Equation (7): `4R(u)R(t) = (2R(u) + R'(u)(t-u))² + (t-u)² (4R(u)D_u(t) - R'(u)²)`. -/
theorem tangent_identity (R : ℤ[X]) (u t : ℤ) :
    4 * R.eval u * R.eval t = (2 * R.eval u + R.derivative.eval u * (t - u)) ^ 2 +
      (t - u) ^ 2 * (4 * R.eval u * (Du R u).eval t - (R.derivative.eval u) ^ 2) := by
  rw [taylor_identity R u t]; ring

/-- For `R(t) = t³ + f` one has `D_u(t) = t + 2u` (Section 3). -/
theorem Du_cubic (f u : ℤ) : Du (X ^ 3 + C f) u = X + C (2 * u) := by
  symm; apply Du_unique
  intro t; simp; ring

/-- For `R(t) = t³ + f`, the auxiliary expression `4R(u)D_u(t) - R'(u)²` equals
`4(u³+f) t - u(u³ - 8f)`; with `t = x²` this is the passage from (8) to (11). -/
theorem aux_cubic (f u t : ℤ) :
    4 * (X ^ 3 + C f : ℤ[X]).eval u * (Du (X ^ 3 + C f) u).eval t -
      ((X ^ 3 + C f : ℤ[X]).derivative.eval u) ^ 2 = 4 * (u ^ 3 + f) * t - u * (u ^ 3 - 8 * f) := by
  rw [Du_cubic]; simp; ring

/-! ## Sums of two squares and property (*) -/

lemma mem_S2_iff_nat (n : ℕ) : (n : ℤ) ∈ S2 ↔ 0 < n ∧ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨h0, y, z, h⟩
    refine ⟨by exact_mod_cast h0, y.natAbs, z.natAbs, ?_⟩
    have : ((n:ℕ):ℤ) = ((y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, sq_abs]; exact h
    exact_mod_cast this
  · rintro ⟨h0, x, y, h⟩
    exact ⟨by exact_mod_cast h0, x, y, by exact_mod_cast h⟩

/-- The classical characterisation of `𝒮₂` quoted in Section 2 (from Mathlib's
`Nat.eq_sq_add_sq_iff`): a positive integer is a sum of two squares iff every prime
`p ≡ 3 (mod 4)` occurs in it with an even exponent. -/
theorem S2_iff_prime_exponents (n : ℤ) :
    n ∈ S2 ↔ 0 < n ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p n.toNat) := by
  by_cases hn : 0 < n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
    rw [mem_S2_iff_nat, Int.toNat_natCast, Nat.eq_sq_add_sq_iff]
    have hm : 0 < m := by exact_mod_cast hn
    simp only [hm, hn, true_and]
    constructor
    · intro h p hp h3
      by_cases hd : p ∣ m
      · exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hm.ne'⟩) h3
      · rw [padicValNat.eq_zero_of_not_dvd hd]; exact ⟨0, rfl⟩
    · intro h p hp h3
      exact h p (Nat.prime_of_mem_primeFactors hp) h3
  · constructor
    · rintro ⟨h, _⟩; exact absurd h hn
    · rintro ⟨h, _⟩; exact absurd h hn

/-- Property (*): if `a, b` are positive integers and `𝒮₂` contains two of the integers
`a, b, ab`, then it contains all three of them. -/
theorem property_star (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (a ∈ S2 → b ∈ S2 → a * b ∈ S2) ∧ (a ∈ S2 → a * b ∈ S2 → b ∈ S2) ∧
      (b ∈ S2 → a * b ∈ S2 → a ∈ S2) := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
  have ha' : a' ≠ 0 := by rintro rfl; simp at ha
  have hb' : b' ≠ 0 := by rintro rfl; simp at hb
  have hab : 0 < (a' : ℤ) * b' := mul_pos ha hb
  have key : ∀ p : ℕ, p.Prime → padicValNat p (a' * b') = padicValNat p a' + padicValNat p b' :=
    fun p hp => by have := Fact.mk hp; exact padicValNat.mul ha' hb'
  have hcast : ((a' : ℤ) * b').toNat = a' * b' := by rw [← Nat.cast_mul, Int.toNat_natCast]
  simp only [S2_iff_prime_exponents, hcast, Int.toNat_natCast, ha, hb, hab, true_and]
  refine ⟨fun h1 h2 p hp h3 => ?_, fun h1 h2 p hp h3 => ?_, fun h1 h2 p hp h3 => ?_⟩
  · rw [key p hp]; exact (h1 p hp h3).add (h2 p hp h3)
  · have := h2 p hp h3; rw [key p hp] at this
    exact (Nat.even_add.mp this).mp (h1 p hp h3)
  · have := h2 p hp h3; rw [key p hp] at this
    exact (Nat.even_add.mp this).mpr (h1 p hp h3)

lemma mem_S2_of_sq_add_sq {n : ℤ} (A B : ℤ) (h : n = A ^ 2 + B ^ 2) (hn : n ≠ 0) : n ∈ S2 :=
  ⟨lt_of_le_of_ne (by rw [h]; positivity) hn.symm, A, B, h⟩

lemma sq_add_sq_mod_four_ne_three (A B : ℤ) : (A ^ 2 + B ^ 2) % 4 ≠ 3 := by
  have hA : A % 4 = 0 ∨ A % 4 = 1 ∨ A % 4 = 2 ∨ A % 4 = 3 := by omega
  have hB : B % 4 = 0 ∨ B % 4 = 1 ∨ B % 4 = 2 ∨ B % 4 = 3 := by omega
  rcases hA with h | h | h | h <;> rcases hB with h' | h' | h' | h' <;>
    simp [pow_two, Int.add_emod, Int.mul_emod, h, h']

lemma sq_add_sq_split_odd_even {A B n : ℤ} (h : A ^ 2 + B ^ 2 = n) (hn : n % 4 = 1) :
    ∃ A' B', A' ^ 2 + B' ^ 2 = n ∧ Odd A' ∧ Even B' := by
  rcases Int.even_or_odd A with hA | hA <;> rcases Int.even_or_odd B with hB | hB
  · obtain ⟨k, rfl⟩ := hA; obtain ⟨l, rfl⟩ := hB
    exfalso; have : n = 4 * (k ^ 2 + l ^ 2) := by rw [← h]; ring
    omega
  · exact ⟨B, A, by rw [← h]; ring, hB, hA⟩
  · exact ⟨A, B, h, hA, hB⟩
  · obtain ⟨k, rfl⟩ := hA; obtain ⟨l, rfl⟩ := hB
    exfalso; have : n = 4 * (k ^ 2 + k + l ^ 2 + l) + 2 := by rw [← h]; ring
    omega

lemma sq_add_sq_even_of_mod_four_zero {A B n : ℤ} (h : A ^ 2 + B ^ 2 = n) (hn : n % 4 = 0) :
    Even A ∧ Even B := by
  rcases Int.even_or_odd A with hA | hA <;> rcases Int.even_or_odd B with hB | hB
  · exact ⟨hA, hB⟩
  all_goals exfalso
  · obtain ⟨k, rfl⟩ := hA; obtain ⟨l, rfl⟩ := hB
    have : n = 4 * (k ^ 2 + l ^ 2 + l) + 1 := by rw [← h]; ring
    omega
  · obtain ⟨k, rfl⟩ := hA; obtain ⟨l, rfl⟩ := hB
    have : n = 4 * (k ^ 2 + k + l ^ 2) + 1 := by rw [← h]; ring
    omega
  · obtain ⟨k, rfl⟩ := hA; obtain ⟨l, rfl⟩ := hB
    have : n = 4 * (k ^ 2 + k + l ^ 2 + l) + 2 := by rw [← h]; ring
    omega

/-! ## A Pell-equation lemma with congruence conditions

This replaces the external results [11, Proposition 5.4] and [11, Proposition 3.14]
used in the proofs of Propositions 2.2 and 4.2: from one solution of
`X² - d V² = δ` (`d > 0` not a square, `δ ≠ 0`) we produce infinitely many solutions in
the same residue class modulo any prescribed `N ≠ 0`. -/

/-- The action of a solution `g = (s, t)` of `s² - d t² = 1` on pairs:
`(X, V) ↦ (sX + d t V, t X + s V)`. -/
def pellAct {d : ℤ} (g : Pell.Solution₁ d) (v : ℤ × ℤ) : ℤ × ℤ :=
  (g.x * v.1 + d * g.y * v.2, g.y * v.1 + g.x * v.2)

lemma pellAct_mul {d : ℤ} (g h : Pell.Solution₁ d) (v : ℤ × ℤ) :
    pellAct (g * h) v = pellAct g (pellAct h v) := by
  simp only [pellAct, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Prod.mk.injEq]
  constructor <;> ring

lemma pellAct_norm {d : ℤ} (g : Pell.Solution₁ d) (v : ℤ × ℤ) :
    (pellAct g v).1 ^ 2 - d * (pellAct g v).2 ^ 2 = v.1 ^ 2 - d * v.2 ^ 2 := by
  have := g.prop
  simp only [pellAct]
  linear_combination (v.1 ^ 2 - d * v.2 ^ 2) * this

/-- A nontrivial Pell unit congruent to `(1, 0)` modulo `N`. -/
lemma exists_pell_unit_cong (d N : ℤ) (hd : 0 < d) (hsq : ¬ IsSquare d) (hN : N ≠ 0) :
    ∃ g : Pell.Solution₁ d, 0 < g.x ∧ 0 < g.y ∧ N ∣ g.x - 1 ∧ N ∣ g.y := by
  obtain ⟨a, ha1, ha2⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd hsq
  have : NeZero N.natAbs := ⟨Int.natAbs_ne_zero.mpr hN⟩
  let f : ℕ → ZMod N.natAbs × ZMod N.natAbs := fun n => (((a ^ n).x : ℤ), ((a ^ n).y : ℤ))
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have main : ∀ i j : ℕ, i < j → f i = f j →
      ∃ g : Pell.Solution₁ d, 0 < g.x ∧ 0 < g.y ∧ N ∣ g.x - 1 ∧ N ∣ g.y := by
    intro i j hlt hf
    obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
    refine ⟨a ^ (k + 1), Pell.Solution₁.x_pow_pos (by omega) _,
      Pell.Solution₁.y_pow_succ_pos (by omega) ha2 _, ?_, ?_⟩
    all_goals
      have hx : ((a ^ i).x : ZMod N.natAbs) = ((a ^ (i + (k + 1))).x : ℤ) := congrArg Prod.fst hf
      have hy : ((a ^ i).y : ZMod N.natAbs) = ((a ^ (i + (k + 1))).y : ℤ) := congrArg Prod.snd hf
      have hk : a ^ (k + 1) = a ^ (i + (k + 1)) * (a ^ i)⁻¹ := by
        rw [pow_add]; group
      have hp := (a ^ i).prop
      rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [hk]
      simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Pell.Solution₁.x_inv,
        Pell.Solution₁.y_inv]
      push_cast
      rw [← hx, ← hy]
    · have hp' : (((a ^ i).x ^ 2 - d * (a ^ i).y ^ 2 : ℤ) : ZMod N.natAbs) = 1 := by
        rw [hp]; simp
      push_cast at hp'
      linear_combination hp'
    · ring
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact main i j h hf
  · exact main j i h hf.symm

/-- If `d > 0` is not a square, `δ ≠ 0`, and `X₀² - d V₀² = δ`, then for every `N ≠ 0`
there are infinitely many integer solutions `(X, V)` of `X² - d V² = δ` with
`X ≡ X₀` and `V ≡ V₀ (mod N)`. -/
theorem pell_orbit_infinite (d δ N X0 V0 : ℤ) (hd : 0 < d) (hsq : ¬ IsSquare d) (hN : N ≠ 0)
    (h0 : X0 ^ 2 - d * V0 ^ 2 = δ) (hδ : δ ≠ 0) :
    {XV : ℤ × ℤ | XV.1 ^ 2 - d * XV.2 ^ 2 = δ ∧ N ∣ XV.1 - X0 ∧ N ∣ XV.2 - V0}.Infinite := by
  obtain ⟨g, hgx, hgy, hgx1, hgy0⟩ := exists_pell_unit_cong d N hd hsq hN
  let orb : ℕ → ℤ × ℤ := fun n => pellAct (g ^ n) (X0, V0)
  have hsucc : ∀ n, orb (n + 1) = pellAct g (orb n) := fun n => by
    simp only [orb, pow_succ', pellAct_mul]
  have hnorm : ∀ n, (orb n).1 ^ 2 - d * (orb n).2 ^ 2 = δ := fun n => by
    simp only [orb, pellAct_norm]; exact h0
  have hcong : ∀ n, N ∣ (orb n).1 - X0 ∧ N ∣ (orb n).2 - V0 := by
    intro n
    induction n with
    | zero => simp [orb, pellAct]
    | succ n ih =>
      rw [hsucc]
      obtain ⟨h1, h2⟩ := ih
      constructor
      · have : (pellAct g (orb n)).1 - X0 =
            (g.x - 1) * (orb n).1 + d * g.y * (orb n).2 + ((orb n).1 - X0) := by
          simp only [pellAct]; ring
        rw [this]
        exact ((dvd_mul_of_dvd_left hgx1 _).add
          (Dvd.dvd.mul_right (Dvd.dvd.mul_left hgy0 d) _)).add h1
      · have : (pellAct g (orb n)).2 - V0 =
            g.y * (orb n).1 + (g.x - 1) * (orb n).2 + ((orb n).2 - V0) := by
          simp only [pellAct]; ring
        rw [this]
        exact ((dvd_mul_of_dvd_left hgy0 _).add (dvd_mul_of_dvd_left hgx1 _)).add h2
  have hinj : Function.Injective orb := by
    have fix : ∀ n k, orb (n + (k + 1)) ≠ orb n := by
      intro n k heq
      have e : orb (n + (k + 1)) = pellAct (g ^ (k + 1)) (orb n) := by
        simp only [orb, ← pellAct_mul, ← pow_add, add_comm]
      rw [e] at heq
      set h := g ^ (k + 1)
      have hy : 0 < h.y := Pell.Solution₁.y_pow_succ_pos hgx hgy k
      have hp := h.prop
      have hx1 : h.x ≠ 1 := by
        intro h1; rw [h1] at hp; nlinarith
      set X := (orb n).1
      set V := (orb n).2
      have e1 : h.x * X + d * h.y * V - X = 0 := by
        have := congrArg Prod.fst heq; simp only [pellAct] at this; linarith
      have e2 : h.y * X + h.x * V - V = 0 := by
        have := congrArg Prod.snd heq; simp only [pellAct] at this; linarith
      have hV : V * (2 - 2 * h.x) = 0 := by
        linear_combination (h.x - 1) * e2 - h.y * e1 - V * hp
      have hV0 : V = 0 := by
        rcases mul_eq_zero.mp hV with h' | h'
        · exact h'
        · exact absurd (by linarith) hx1
      have hX0 : X = 0 := by
        rw [hV0] at e2
        have : h.y * X = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hy.ne'
      apply hδ
      rw [← hnorm n]
      show X ^ 2 - d * V ^ 2 = 0
      rw [hX0, hV0]; ring
    intro m n hmn
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
      exact fix m k hmn.symm
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + (k + 1) := ⟨m - n - 1, by omega⟩
      exact fix n k hmn
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨n, rfl⟩; exact ⟨hnorm n, hcong n⟩)


/-! ## Finiteness helpers -/

lemma finite_setOf_mul_sq_eq (k g : ℤ) (hk : k ≠ 0) : {v : ℤ | k * v ^ 2 = g}.Finite := by
  apply (Set.finite_Icc (-|g|) |g|).subset
  intro v hv
  simp only [mem_setOf_iff'] at hv
  have h1 : |v| ≤ v ^ 2 := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · have : 1 ≤ |v| := Int.one_le_abs hv0
      nlinarith [sq_abs v]
  have h2 : v ^ 2 ≤ |g| := by
    rw [← hv, abs_mul, abs_of_nonneg (sq_nonneg v)]
    have : 1 ≤ |k| := Int.one_le_abs hk
    nlinarith [sq_nonneg v]
  exact abs_le.mp (h1.trans h2)

/-- If `S` is an infinite set of pairs `(x, v)` with `k v² = g(x)` (`k ≠ 0`), then
infinitely many distinct `x` occur. -/
lemma infinite_fst_of_sq {S : Set (ℤ × ℤ)} (hS : S.Infinite) (k : ℤ) (g : ℤ → ℤ) (hk : k ≠ 0)
    (hfib : ∀ xv ∈ S, k * xv.2 ^ 2 = g xv.1) : (Prod.fst '' S).Infinite := by
  intro hfin
  apply hS
  apply (hfin.prod (hfin.biUnion fun x _ => finite_setOf_mul_sq_eq k (g x) hk)).subset
  rintro ⟨x, v⟩ hxv
  refine ⟨⟨_, hxv, rfl⟩, ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨x, ⟨_, hxv, rfl⟩, hfib _ hxv⟩

lemma infinite_of_fst_infinite {T : Set (ℤ × ℤ × ℤ)} {S : Set ℤ} (hS : S.Infinite)
    (h : ∀ x ∈ S, ∃ y z, (x, y, z) ∈ T) : T.Infinite := by
  intro hT
  apply hS
  apply (hT.image Prod.fst).subset
  intro x hx
  obtain ⟨y, z, h⟩ := h x hx
  exact ⟨_, h, rfl⟩

lemma infinite_image_neg_sq {S : Set ℤ} (hS : S.Infinite) :
    ((fun w : ℤ => -w ^ 2) '' S).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image abs).bddAbove
  apply hS
  apply (Set.finite_Icc (-M) M).subset
  intro w hw
  have h1 : |(-w ^ 2)| ≤ M := hM ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have h2 : |w| ≤ w ^ 2 := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have : 1 ≤ |w| := Int.one_le_abs hw0
      nlinarith [sq_abs w]
  rw [abs_neg, abs_of_nonneg (sq_nonneg w)] at h1
  exact abs_le.mp (h2.trans h1)

/-! ## Section 2: the sum of two squares case -/

/-- **Proposition 2.1.** Let `R(t)` and `Q(x)` be non-constant polynomials with integer
coefficients, and let `u ∈ ℤ` satisfy `R(u) ∈ 𝒮₂`. Define `D_u` by (6). If the auxiliary
equation (8) `4R(u)D_u(Q(x)) - R'(u)² = v²` has infinitely many integer solutions
`(x, v)`, then `R(Q(x)) ∈ 𝒮₂` for infinitely many integers `x`. -/
theorem proposition_2_1 (R Q : ℤ[X]) (hR : 0 < R.natDegree) (hQ : 0 < Q.natDegree) (u : ℤ)
    (hu : R.eval u ∈ S2)
    (haux : {xv : ℤ × ℤ | 4 * R.eval u * (Du R u).eval (Q.eval xv.1) -
      (R.derivative.eval u) ^ 2 = xv.2 ^ 2}.Infinite) :
    {x : ℤ | R.eval (Q.eval x) ∈ S2}.Infinite := by
  have hX := infinite_fst_of_sq haux 1
    (fun x => 4 * R.eval u * (Du R u).eval (Q.eval x) - (R.derivative.eval u) ^ 2) one_ne_zero
    (fun xv h => by rw [one_mul]; exact h.symm)
  have hRQ : R.comp Q ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_comp, natDegree_zero] at this
    exact (Nat.mul_pos hR hQ).ne' this
  have hZ : {x : ℤ | (R.comp Q).IsRoot x}.Finite := finite_setOf_isRoot' hRQ
  intro hfin
  apply hX
  refine (hfin.union hZ).subset ?_
  rintro x ⟨⟨x', v⟩, hv, rfl⟩
  by_cases hx : (R.comp Q).IsRoot x'
  · exact Or.inr hx
  left
  simp only [mem_setOf_iff', IsRoot, eval_comp] at hv hx ⊢
  obtain ⟨hm, y, z, hyz⟩ := hu
  have h4m : 4 * R.eval u ∈ S2 := ⟨by positivity, 2 * y, 2 * z, by rw [hyz]; ring⟩
  have hid := tangent_identity R u (Q.eval x')
  rw [hv] at hid
  have hprod : 4 * R.eval u * R.eval (Q.eval x') ∈ S2 :=
    mem_S2_of_sq_add_sq (2 * R.eval u + R.derivative.eval u * (Q.eval x' - u))
      ((Q.eval x' - u) * v) (by rw [hid]; ring) (mul_ne_zero (by positivity) hx)
  have hn : 0 < R.eval (Q.eval x') := pos_of_mul_pos_right hprod.1 (by positivity)
  exact (property_star _ _ (by positivity) hn).2.1 h4m hprod

/-- `4a` is a square only if `a` is. -/
lemma isSquare_of_isSquare_four_mul {a : ℤ} (h : IsSquare (4 * a)) : IsSquare a := by
  obtain ⟨r, hr⟩ := h
  rcases Int.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k, by linarith⟩
  · exfalso
    have : (2 * k + 1) * (2 * k + 1) = 4 * (k ^ 2 + k) + 1 := by ring
    omega

/-- **Proposition 2.2.** Let `a, b, c ∈ ℤ`. Assume that (a) either `a = 0`, or `a > 0`
and `a` is not a perfect square, (b) `b² - 4ac ≠ 0`, and (c) equation (9)
`a x² + b x + c = v²` has an integer solution `(x₀, v₀)`. Then (9) has infinitely many
integer solutions `(x, v)`, with infinitely many distinct values of `x`.

(The paper quotes [11, Proposition 5.4] for the case `a > 0`; here that case is proved
from `pell_orbit_infinite`.) -/
theorem proposition_2_2 (a b c : ℤ) (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a))
    (hb : b ^ 2 - 4 * a * c ≠ 0) (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = v0 ^ 2) :
    {xv : ℤ × ℤ | a * xv.1 ^ 2 + b * xv.1 + c = xv.2 ^ 2}.Infinite ∧
      {x : ℤ | ∃ v : ℤ, a * x ^ 2 + b * x + c = v ^ 2}.Infinite := by
  obtain ⟨x0, v0, h0⟩ := hc
  have hpairs : {xv : ℤ × ℤ | a * xv.1 ^ 2 + b * xv.1 + c = xv.2 ^ 2}.Infinite := by
    rcases ha with rfl | ⟨ha, hsq⟩
    · have hb0 : b ≠ 0 := by rintro rfl; simp at hb
      let f : ℤ → ℤ × ℤ := fun k => (x0 + 2 * v0 * k + b * k ^ 2, v0 + b * k)
      have hf : Function.Injective f := by
        intro k l hkl
        have := congrArg Prod.snd hkl
        simp only [f] at this
        exact mul_left_cancel₀ hb0 (by linarith)
      apply (Set.infinite_range_of_injective hf).mono
      rintro _ ⟨k, rfl⟩
      simp only [f, mem_setOf_iff']
      linear_combination h0
    · have hsq4 : ¬ IsSquare (4 * a) := fun h => hsq (isSquare_of_isSquare_four_mul h)
      have hP := pell_orbit_infinite (4 * a) (b ^ 2 - 4 * a * c) (2 * a) (2 * a * x0 + b) v0
        (by positivity) hsq4 (by positivity) (by linear_combination 4 * a * h0) hb
      let φ : ℤ × ℤ → ℤ × ℤ := fun XV => ((XV.1 - b) / (2 * a), XV.2)
      have hrec : ∀ XV ∈ {XV : ℤ × ℤ | XV.1 ^ 2 - 4 * a * XV.2 ^ 2 = b ^ 2 - 4 * a * c ∧
          2 * a ∣ XV.1 - (2 * a * x0 + b) ∧ 2 * a ∣ XV.2 - v0},
          XV.1 = 2 * a * (φ XV).1 + b := by
        rintro ⟨X, V⟩ ⟨_, h2, _⟩
        have : 2 * a ∣ X - b := by
          have := h2.add (dvd_mul_right (2 * a) x0); ring_nf at this ⊢; exact this
        simp only [φ]
        rw [Int.mul_ediv_cancel' this]; ring
      apply (hP.image (f := φ) ?_).mono
      · rintro _ ⟨⟨X, V⟩, hXV, rfl⟩
        have hX := hrec _ hXV
        obtain ⟨h1, -, -⟩ := hXV
        show a * (φ (X, V)).1 ^ 2 + b * (φ (X, V)).1 + c = (φ (X, V)).2 ^ 2
        simp only at hX h1
        rw [hX] at h1
        have : 4 * a * (a * (φ (X, V)).1 ^ 2 + b * (φ (X, V)).1 + c - V ^ 2) = 0 := by
          linear_combination h1
        simp only [φ] at this ⊢
        have := (mul_eq_zero.mp this).resolve_left (by positivity)
        linarith
      · intro p hp q hq hpq
        have e1 := hrec p hp
        have e2 := hrec q hq
        rw [hpq] at e1
        exact Prod.ext (by rw [e1, e2]) (by simpa [φ] using congrArg Prod.snd hpq)
  refine ⟨hpairs, ?_⟩
  have := infinite_fst_of_sq hpairs 1 (fun x => a * x ^ 2 + b * x + c) one_ne_zero
    (fun xv h => by rw [one_mul]; exact h.symm)
  apply this.mono
  rintro _ ⟨⟨x, v⟩, h, rfl⟩
  exact ⟨v, h⟩

/-- The admissible degree pairs `(deg R, deg Q) ∈ {(3,1), (4,1), (3,2)}` of
Algorithms 2.1 and 4.1. -/
def AdmissibleDegrees (R Q : ℤ[X]) : Prop :=
  (R.natDegree = 3 ∧ Q.natDegree = 1) ∨ (R.natDegree = 4 ∧ Q.natDegree = 1) ∨
    (R.natDegree = 3 ∧ Q.natDegree = 2)

/-- For admissible degrees, `K · D_u(Q(x)) - L` is a polynomial of degree at most two in
`x`: this is why the auxiliary equations (8) and (26) take the forms (9) and (29). -/
theorem aux_equation_quadratic (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u K L : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, K * (Du R u).eval (Q.eval x) - L = a * x ^ 2 + b * x + c := by
  set P : ℤ[X] := C K * (Du R u).comp Q - C L with hPdef
  have hP : P.natDegree ≤ 2 := by
    have h1 : ((Du R u).comp Q).natDegree ≤ 2 := by
      refine natDegree_comp_le.trans ?_
      have := natDegree_Du_le R u
      rcases hdeg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> rw [h1] at this <;>
        nlinarith
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans h1) (by simp))
  refine ⟨P.coeff 2, P.coeff 1, P.coeff 0, fun x => ?_⟩
  have e : P.eval x = K * (Du R u).eval (Q.eval x) - L := by simp [P, eval_comp]
  rw [← e, eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]; ring

/-- **Algorithm 2.1, Step 2.** For admissible `(deg R, deg Q)` and any `u`, the auxiliary
equation (8) can be written in the form (9) `a x² + b x + c = v²`. -/
theorem algorithm_2_1_step2 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, 4 * R.eval u * (Du R u).eval (Q.eval x) -
      (R.derivative.eval u) ^ 2 = a * x ^ 2 + b * x + c :=
  aux_equation_quadratic R Q hdeg u _ _

/-- **Algorithm 2.1 (correctness of the output).** Let `(deg R, deg Q)` be admissible.
If Step 1 finds `u` with `R(u) ∈ 𝒮₂`, Step 2 writes (8) as `a x² + b x + c = v²`, and
conditions (a), (b), (c) of Proposition 2.2 hold (so that the algorithm stops), then
`P(x) = R(Q(x)) ∈ 𝒮₂` for infinitely many integers `x`. -/
theorem algorithm_2_1 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u a b c : ℤ)
    (hu : R.eval u ∈ S2)
    (habc : ∀ x : ℤ, 4 * R.eval u * (Du R u).eval (Q.eval x) - (R.derivative.eval u) ^ 2 =
      a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < a ∧ ¬ IsSquare a)) (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = v0 ^ 2) :
    {x : ℤ | R.eval (Q.eval x) ∈ S2}.Infinite := by
  have hR : 0 < R.natDegree := by
    rcases hdeg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hQ : 0 < Q.natDegree := by
    rcases hdeg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  refine proposition_2_1 R Q hR hQ u hu ?_
  convert (proposition_2_2 a b c ha hb hc).1 using 1
  ext xv
  simp only [mem_setOf_iff', habc]

/-- **Seed test for Algorithm 2.1 in the linear case `a = 0`** (Section 2): if `b ≠ 0`,
then `b x + c = v²` has an integer solution iff `v² ≡ c (mod |b|)` for some
`0 ≤ v < |b|`; a successful residue gives `x = (v² - c)/b`. -/
theorem algorithm_2_1_linear_seed_test (b c : ℤ) (hb : b ≠ 0) :
    (∃ x v : ℤ, b * x + c = v ^ 2) ↔ ∃ v : ℤ, 0 ≤ v ∧ v < |b| ∧ b ∣ v ^ 2 - c := by
  constructor
  · rintro ⟨x, v, h⟩
    have hb' : |b| ≠ 0 := abs_ne_zero.mpr hb
    refine ⟨v % |b|, Int.emod_nonneg v hb', Int.emod_lt_of_pos v (abs_pos.mpr hb), ?_⟩
    have h1 : b ∣ v ^ 2 - (v % |b|) ^ 2 :=
      (abs_dvd b _).mp (((Int.mod_modEq v |b|).pow 2).dvd)
    have h2 : b ∣ v ^ 2 - c := ⟨x, by linarith⟩
    have := dvd_sub h2 h1
    ring_nf at this ⊢
    exact this
  · rintro ⟨v, -, -, x, hx⟩
    exact ⟨x, v, by linarith⟩

/-! ## Section 3: application to the shortest open equations -/

lemma not_isSquare_of_lt_of_lt (n k : ℤ) (hk : 0 ≤ k) (h1 : k ^ 2 < n) (h2 : n < (k + 1) ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have e := abs_mul_abs_self r
  have h3 : k < |r| := by
    by_contra h; rw [not_lt] at h; nlinarith [abs_nonneg r]
  have h4 : |r| < k + 1 := by
    by_contra h; rw [not_lt] at h; nlinarith [abs_nonneg r]
  omega

lemma natDegree_cubic (f : ℤ) : (X ^ 3 + C f : ℤ[X]).natDegree = 3 := natDegree_X_pow_add_C

lemma sixth_mod_four_of_even {x : ℤ} (hx : Even x) (f : ℤ) : (x ^ 6 + f) % 4 = f % 4 := by
  obtain ⟨k, rfl⟩ := hx
  have : (k + k) ^ 6 + f = 4 * (16 * k ^ 6) + f := by ring
  omega

/-- Equation (2) `y² + x³y + z² + 1 = 0` is equivalent to (3)
`(x³ + 2y)² + (2z)² = x⁶ - 4`. -/
theorem equation_2_iff_3 (x y z : ℤ) :
    y ^ 2 + x ^ 3 * y + z ^ 2 + 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z) ^ 2 = x ^ 6 - 4 := by
  constructor
  · intro h; linear_combination 4 * h
  · intro h
    have : 4 * (y ^ 2 + x ^ 3 * y + z ^ 2 + 1) = 0 := by linear_combination h
    linarith

/-- The auxiliary computations of Section 3, for `R(t) = t³ + f`, `Q(x) = x²` and the
chosen `u`: equation (11) becomes `a x² + c = v²`, with the indicated values. -/
theorem aux_equations_section_3 (x : ℤ) :
    (4 * ((162 : ℤ) ^ 3 - 4) * x ^ 2 - 162 * (162 ^ 3 - 8 * (-4)) = 17006096 * x ^ 2 - 688752720) ∧
    (4 * ((2 : ℤ) ^ 3 - 4) * x ^ 2 - 2 * (2 ^ 3 - 8 * (-4)) = 16 * x ^ 2 - 80) ∧
    (4 * ((8 : ℤ) ^ 3 + 8) * x ^ 2 - 8 * (8 ^ 3 - 8 * 8) = 2080 * x ^ 2 - 3584) ∧
    (4 * ((2 : ℤ) ^ 3 + 5) * x ^ 2 - 2 * (2 ^ 3 - 8 * 5) = 52 * x ^ 2 + 64) ∧
    (4 * ((2 : ℤ) ^ 3 - 3) * x ^ 2 - 2 * (2 ^ 3 - 8 * (-3)) = 20 * x ^ 2 - 64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The seed `u = 2` fails for `f = -4` (proof of Corollary 3.1): `u = 2` is the smallest
positive integer with `u³ - 4 ∈ 𝒮₂`, but the resulting auxiliary equation
`16x² - 80 = v²` has `a = 16`, a perfect square, so condition (a) fails. -/
theorem corollary_3_1_seed_two_fails :
    (∀ u : ℤ, 0 < u → u ^ 3 - 4 ∈ S2 → 2 ≤ u) ∧ (2 : ℤ) ^ 3 - 4 ∈ S2 ∧
      IsSquare (4 * ((2 : ℤ) ^ 3 - 4)) := by
  refine ⟨fun u hu h => ?_, ⟨by norm_num, 2, 0, by norm_num⟩, ⟨4, by norm_num⟩⟩
  by_contra h'
  have : u = 1 := by omega
  subst this
  exact absurd h.1 (by norm_num)

/-- Corollary 3.1, sum-of-two-squares part: `x⁶ - 4 ∈ 𝒮₂` for infinitely many integers
`x` (Algorithm 2.1 with `R(t) = t³ - 4`, `Q(x) = x²`, `u = 162`). -/
theorem corollary_3_1_sum_of_two_squares : {x : ℤ | x ^ 6 - 4 ∈ S2}.Infinite := by
  have hdeg : AdmissibleDegrees (X ^ 3 + C (-4)) (X ^ 2) :=
    Or.inr (Or.inr ⟨natDegree_cubic _, natDegree_X_pow 2⟩)
  have h := algorithm_2_1 (X ^ 3 + C (-4)) (X ^ 2) hdeg 162 17006096 0 (-688752720)
    (by simp only [eval_add, eval_pow, eval_X, eval_C]
        exact ⟨by norm_num, 350, 2032, by norm_num⟩)
    (fun x => by rw [aux_cubic]; simp; ring)
    (Or.inr ⟨by norm_num, not_isSquare_of_lt_of_lt _ 4123 (by norm_num) (by norm_num)
      (by norm_num)⟩)
    (by norm_num) ⟨22108343594783571, 91171377945572295096, by norm_num⟩
  convert h using 1
  ext x
  simp only [mem_setOf_iff', eval_add, eval_pow, eval_X, eval_C]
  ring_nf

/-- **Corollary 3.1.** Equation (2) `y² + x³y + z² + 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_1 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_of_fst_infinite corollary_3_1_sum_of_two_squares
  rintro x ⟨-, A, B, hAB⟩
  have hodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      obtain ⟨hA, hB⟩ := sq_add_sq_even_of_mod_four_zero hAB.symm
        (by have := sixth_mod_four_of_even hx (-4); omega)
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hA
      obtain ⟨b, rfl⟩ := hB
      have e' : 4 * (a ^ 2 + b ^ 2) = 4 * (4 * (4 * k ^ 6) - 1) := by linear_combination -hAB
      have e : a ^ 2 + b ^ 2 = 4 * (4 * k ^ 6) - 1 := by linarith
      exact sq_add_sq_mod_four_ne_three a b (by omega)
    · exact hx
  obtain ⟨k, rfl⟩ := hodd
  have hmod : (A ^ 2 + B ^ 2) % 4 = 1 := by
    have : (2 * k + 1) ^ 6 - 4 =
        4 * (16 * k ^ 6 + 48 * k ^ 5 + 60 * k ^ 4 + 40 * k ^ 3 + 15 * k ^ 2 + 3 * k - 1) + 1 := by
      ring
    omega
  obtain ⟨A', B', hAB', ⟨j, rfl⟩, ⟨l, rfl⟩⟩ := sq_add_sq_split_odd_even rfl hmod
  refine ⟨j - (4 * k ^ 3 + 6 * k ^ 2 + 3 * k), l, ?_⟩
  show _ = _
  have : 4 * ((j - (4 * k ^ 3 + 6 * k ^ 2 + 3 * k)) ^ 2 +
      (2 * k + 1) ^ 3 * (j - (4 * k ^ 3 + 6 * k ^ 2 + 3 * k)) + l ^ 2 + 1) = 0 := by
    linear_combination hAB' - hAB
  linarith

/-- Algorithm 2.1 with `R(t) = t³ + f` and `Q(w) = 4w²` (as in the proof of Corollary 3.2):
given a seed `u` with `u³ + f ∈ 𝒮₂`, `16(u³+f)` strictly between two consecutive squares,
`u(u³ - 8f) ≠ 0`, and one solution of `16(u³+f) w² - u(u³-8f) = v²`, there are infinitely
many even `x` with `x⁶ + f ∈ 𝒮₂`. -/
lemma even_sixth_add_infinite (f u : ℤ) (hu : u ^ 3 + f ∈ S2) (k : ℤ) (hk : 0 ≤ k)
    (hk1 : k ^ 2 < 16 * (u ^ 3 + f)) (hk2 : 16 * (u ^ 3 + f) < (k + 1) ^ 2)
    (hc : u * (u ^ 3 - 8 * f) ≠ 0) (w0 v0 : ℤ)
    (h0 : 16 * (u ^ 3 + f) * w0 ^ 2 - u * (u ^ 3 - 8 * f) = v0 ^ 2) :
    {x : ℤ | Even x ∧ x ^ 6 + f ∈ S2}.Infinite := by
  have hdeg : AdmissibleDegrees (X ^ 3 + C f) (C 4 * X ^ 2) :=
    Or.inr (Or.inr ⟨natDegree_cubic _, natDegree_C_mul_X_pow 2 (4 : ℤ) (by norm_num)⟩)
  have hpos : 0 < u ^ 3 + f := hu.1
  have h := algorithm_2_1 (X ^ 3 + C f) (C 4 * X ^ 2) hdeg u (16 * (u ^ 3 + f)) 0
    (-(u * (u ^ 3 - 8 * f)))
    (by simpa using hu) (fun x => by rw [aux_cubic]; simp; ring)
    (Or.inr ⟨by positivity, not_isSquare_of_lt_of_lt _ k hk hk1 hk2⟩)
    (by
      have : (16 * (u ^ 3 + f)) ≠ 0 := by positivity
      intro h; apply hc
      have : 4 * (16 * (u ^ 3 + f)) * (u * (u ^ 3 - 8 * f)) = 0 := by linear_combination h
      simpa [hpos.ne'] using this)
    ⟨w0, v0, by linear_combination h0⟩
  apply (h.image (f := fun w => 2 * w) (mul_right_injective₀ two_ne_zero).injOn).mono
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨even_two_mul w, ?_⟩
  simp only [mem_setOf_iff', eval_add, eval_pow, eval_X, eval_C, eval_mul] at hw
  convert hw using 1; ring

/-- Corollary 3.2, sum-of-two-squares part: for each `f ∈ {8, 5, -3}` there are infinitely
many even `x` with `x⁶ + f ∈ 𝒮₂` (seeds `u = 8, 2, 2` and `(w₀, v₀) = (6, 544), (3, 44),
(1, 4)`). -/
theorem corollary_3_2_sum_of_two_squares :
    {x : ℤ | Even x ∧ x ^ 6 + 8 ∈ S2}.Infinite ∧ {x : ℤ | Even x ∧ x ^ 6 + 5 ∈ S2}.Infinite ∧
      {x : ℤ | Even x ∧ x ^ 6 - 3 ∈ S2}.Infinite := by
  refine ⟨?_, ?_, ?_⟩
  · exact even_sixth_add_infinite 8 8 ⟨by norm_num, 22, 6, by norm_num⟩ 91 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) 6 544 (by norm_num)
  · exact even_sixth_add_infinite 5 2 ⟨by norm_num, 3, 2, by norm_num⟩ 14 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) 3 44 (by norm_num)
  · have := even_sixth_add_infinite (-3) 2 ⟨by norm_num, 2, 1, by norm_num⟩ 8 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) 1 4 (by norm_num)
    simpa [← sub_eq_add_neg] using this

/-- Equations (13)–(15) can be rewritten in the form (17)
`(x³ + 2y)² + (2z + e)² = x⁶ + f` with `(e, f) = (0, 8), (1, 5), (1, -3)`, and equation (16)
can be rewritten as (18) `(x³ + 2y + 1)² + (2z)² = (x³ + 1)² - 4`. -/
theorem equations_13_to_16_rewritten (x y z : ℤ) :
    (y ^ 2 + x ^ 3 * y + z ^ 2 - 2 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 0) ^ 2 = x ^ 6 + 8) ∧
    (y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 1) ^ 2 = x ^ 6 + 5) ∧
    (y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1 = 0 ↔ (x ^ 3 + 2 * y) ^ 2 + (2 * z + 1) ^ 2 = x ^ 6 - 3) ∧
    (y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1 = 0 ↔
      (x ^ 3 + 2 * y + 1) ^ 2 + (2 * z) ^ 2 = (x ^ 3 + 1) ^ 2 - 4) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  all_goals first
    | linear_combination 4 * h
    | (have : 4 * (y ^ 2 + x ^ 3 * y + z ^ 2 - 2) = 0 := by linear_combination h
       linarith)
    | (have : 4 * (y ^ 2 + x ^ 3 * y + z ^ 2 + z - 1) = 0 := by linear_combination h
       linarith)
    | (have : 4 * (y ^ 2 + x ^ 3 * y + z ^ 2 + z + 1) = 0 := by linear_combination h
       linarith)
    | (have : 4 * (y ^ 2 + x ^ 3 * y + y + z ^ 2 + 1) = 0 := by linear_combination h
       linarith)

/-- **Corollary 3.2, equation (13).** `y² + x³y + z² - 2 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq13 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 - 2 = 0}.Infinite := by
  apply infinite_of_fst_infinite corollary_3_2_sum_of_two_squares.1
  rintro x ⟨hx, -, A, B, hAB⟩
  obtain ⟨hA, hB⟩ := sq_add_sq_even_of_mod_four_zero hAB.symm
    (by have := sixth_mod_four_of_even hx 8; omega)
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  refine ⟨a - 4 * k ^ 3, b, ?_⟩
  show _ = _
  have : 4 * ((a - 4 * k ^ 3) ^ 2 + (k + k) ^ 3 * (a - 4 * k ^ 3) + b ^ 2 - 2) = 0 := by
    linear_combination -hAB
  linarith

/-- Equations (14) and (15): from `x` even with `x⁶ + f ∈ 𝒮₂`, `f ≡ 1 (mod 4)`, produce
`y, z` with `(x³ + 2y)² + (2z + 1)² = x⁶ + f`. -/
lemma even_sixth_rep_odd {x f : ℤ} (hx : Even x) (hf : f % 4 = 1) (h : x ^ 6 + f ∈ S2) :
    ∃ y z : ℤ, (x ^ 3 + 2 * y) ^ 2 + (2 * z + 1) ^ 2 = x ^ 6 + f := by
  obtain ⟨-, A, B, hAB⟩ := h
  obtain ⟨A', B', hAB', ⟨j, rfl⟩, ⟨l, rfl⟩⟩ := sq_add_sq_split_odd_even hAB.symm
    (by have := sixth_mod_four_of_even hx f; omega)
  obtain ⟨k, rfl⟩ := hx
  exact ⟨l - 4 * k ^ 3, j, by linear_combination hAB'⟩

/-- **Corollary 3.2, equation (14).** `y² + x³y + z² + z - 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq14 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 - 1 = 0}.Infinite := by
  apply infinite_of_fst_infinite corollary_3_2_sum_of_two_squares.2.1
  rintro x ⟨hx, h⟩
  obtain ⟨y, z, hyz⟩ := even_sixth_rep_odd hx (by norm_num) h
  exact ⟨y, z, ((equations_13_to_16_rewritten x y z).2.1.mpr hyz)⟩

/-- **Corollary 3.2, equation (15).** `y² + x³y + z² + z + 1 = 0` has infinitely many integer
solutions. -/
theorem corollary_3_2_eq15 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 + 1 = 0}.Infinite := by
  apply infinite_of_fst_infinite corollary_3_2_sum_of_two_squares.2.2
  rintro x ⟨hx, h⟩
  rw [sub_eq_add_neg] at h
  obtain ⟨y, z, hyz⟩ := even_sixth_rep_odd hx (by norm_num) h
  exact ⟨y, z, ((equations_13_to_16_rewritten x y z).2.2.1.mpr (by linear_combination hyz))⟩

/-- **Corollary 3.2, equation (16).** `y² + x³y + y + z² + 1 = 0` has infinitely many integer
solutions (via `x = -w²` and `P(-w²) = (w⁶ - 3)(w⁶ + 1)`). -/
theorem corollary_3_2_eq16 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite := by
  apply infinite_of_fst_infinite (infinite_image_neg_sq corollary_3_2_sum_of_two_squares.2.2)
  rintro _ ⟨w, ⟨hw, hS⟩, rfl⟩
  have hP : (w ^ 6 - 3) * (w ^ 6 + 1) ∈ S2 :=
    (property_star _ _ hS.1 (by positivity)).1 hS
      ⟨by positivity, w ^ 3, 1, by ring⟩
  obtain ⟨-, A, B, hAB⟩ := hP
  obtain ⟨k, rfl⟩ := hw
  have hmod : (A ^ 2 + B ^ 2) % 4 = 1 := by
    have : ((k + k) ^ 6 - 3) * ((k + k) ^ 6 + 1) = 4 * (1024 * k ^ 12 - 32 * k ^ 6 - 1) + 1 := by
      ring
    omega
  obtain ⟨A', B', hAB', ⟨j, rfl⟩, ⟨l, rfl⟩⟩ := sq_add_sq_split_odd_even rfl hmod
  refine ⟨j + 32 * k ^ 6, l, ?_⟩
  show _ = _
  have : 4 * ((j + 32 * k ^ 6) ^ 2 + (-(k + k) ^ 2) ^ 3 * (j + 32 * k ^ 6) + (j + 32 * k ^ 6) +
      l ^ 2 + 1) = 0 := by
    linear_combination hAB' - hAB
  linarith

/-- **Corollary 3.2.** Each of the equations (13)–(16) has infinitely many integer
solutions. -/
theorem corollary_3_2 :
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 - 2 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 - 1 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.2 ^ 2 + s.2.2 + 1 = 0}.Infinite ∧
    {s : ℤ × ℤ × ℤ | s.2.1 ^ 2 + s.1 ^ 3 * s.2.1 + s.2.1 + s.2.2 ^ 2 + 1 = 0}.Infinite :=
  ⟨corollary_3_2_eq13, corollary_3_2_eq14, corollary_3_2_eq15, corollary_3_2_eq16⟩

/-- The closing remark of Section 3 on `y² + z² = x⁶ + 3`: with `R(t) = t³ + 3` and
`Q(x) = x²`, any `u` with `R(u) ∈ 𝒮₂` must be odd, and for odd `u` the auxiliary equation
(11) `4(u³+3)x² - u(u³-24) = v²` has no integer solutions (its left-hand side is
`≡ 3 (mod 4)`). Hence Algorithm 2.1 cannot resolve this equation. -/
theorem remark_x6_plus_3 :
    (∀ u : ℤ, u ^ 3 + 3 ∈ S2 → Odd u) ∧
      (∀ u : ℤ, Odd u → ∀ x v : ℤ, 4 * (u ^ 3 + 3) * x ^ 2 - u * (u ^ 3 - 24) ≠ v ^ 2) := by
  constructor
  · rintro u ⟨-, A, B, hAB⟩
    rcases Int.even_or_odd u with ⟨k, rfl⟩ | hu
    · exfalso
      have : (k + k) ^ 3 + 3 = 4 * (2 * k ^ 3) + 3 := by ring
      exact sq_add_sq_mod_four_ne_three A B (by omega)
    · exact hu
  · rintro u ⟨k, rfl⟩ x v h
    have e : 4 * ((2 * k + 1) ^ 3 + 3) * x ^ 2 - (2 * k + 1) * ((2 * k + 1) ^ 3 - 24) =
        4 * (2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k + 2) * x ^ 2 - 4 * k ^ 4 - 8 * k ^ 3 - 6 * k ^ 2 +
          10 * k + 5) + 3 := by ring
    exact sq_add_sq_mod_four_ne_three v 0 (by rw [← h]; omega)

/-! ## Section 4: general binary quadratic forms -/

/-- The algebraic identity behind the parametrisation (25):
`F(rp + v(Bp + 2Cq), rq - v(2Ap + Bq)) = F(p, q) (r² - Δ v²)`. -/
lemma bqf_tangent_identity (A B C p q r v : ℤ) :
    bqf A B C (r * p + v * (B * p + 2 * C * q)) (r * q - v * (2 * A * p + B * q)) =
      bqf A B C p q * (r ^ 2 - (B ^ 2 - 4 * A * C) * v ^ 2) := by
  unfold bqf; ring

/-- **Proposition 4.1, recovery formulas (28).** Assume (21), i.e.
`m = R(u) = F(p, q) ≠ 0`, let `r = R'(u)`. For every pair `(x, v)` satisfying (26)
`4 m D_u(Q(x)) - r² = -Δ v²` and the congruences (27), the integers `y, z` given by (28)
satisfy `F(y, z) = R(Q(x))`. (Exact integer division is used; the congruences guarantee that
the quotients are integers.) -/
theorem proposition_4_1_recovery (A B C : ℤ) (R Q : ℤ[X]) (u p q m r : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (x v : ℤ)
    (haux : 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = -(B ^ 2 - 4 * A * C) * v ^ 2)
    (hc1 : 2 * |m| ∣ r * p + v * (B * p + 2 * C * q))
    (hc2 : 2 * |m| ∣ r * q - v * (2 * A * p + B * q)) :
    bqf A B C (p + (Q.eval x - u) * ((r * p + v * (B * p + 2 * C * q)) / (2 * m)))
      (q + (Q.eval x - u) * ((r * q - v * (2 * A * p + B * q)) / (2 * m))) =
      R.eval (Q.eval x) := by
  have habs : 2 * |m| = |2 * m| := by rw [abs_mul, abs_two]
  rw [habs, abs_dvd] at hc1 hc2
  have hl := Int.mul_ediv_cancel' hc1
  have hu := Int.mul_ediv_cancel' hc2
  generalize (r * p + v * (B * p + 2 * C * q)) / (2 * m) = l at hl ⊢
  generalize (r * q - v * (2 * A * p + B * q)) / (2 * m) = w at hu ⊢
  set D := (Du R u).eval (Q.eval x)
  set s := Q.eval x - u
  have h2m : (2 * m) ≠ 0 := mul_ne_zero two_ne_zero hm0
  have hlin : 2 * A * p * l + B * (p * w + q * l) + 2 * C * q * w = r := by
    apply mul_left_cancel₀ h2m
    calc 2 * m * (2 * A * p * l + B * (p * w + q * l) + 2 * C * q * w)
        = (2 * A * p + B * q) * (2 * m * l) + (B * p + 2 * C * q) * (2 * m * w) := by ring
      _ = (2 * A * p + B * q) * (r * p + v * (B * p + 2 * C * q)) +
          (B * p + 2 * C * q) * (r * q - v * (2 * A * p + B * q)) := by rw [hl, hu]
      _ = 2 * r * bqf A B C p q := by unfold bqf; ring
      _ = 2 * m * r := by rw [← hmF]; ring
  have hquad : bqf A B C l w = D := by
    have h4 : (4 * m * m) ≠ 0 := by positivity
    apply mul_left_cancel₀ h4
    calc 4 * m * m * bqf A B C l w = bqf A B C (2 * m * l) (2 * m * w) := by unfold bqf; ring
      _ = m * (r ^ 2 - (B ^ 2 - 4 * A * C) * v ^ 2) := by
          rw [hl, hu, bqf_tangent_identity, ← hmF]
      _ = 4 * m * m * D := by linear_combination -m * haux
  have key : bqf A B C (p + s * l) (q + s * w) =
      bqf A B C p q + s * (2 * A * p * l + B * (p * w + q * l) + 2 * C * q * w) +
        s ^ 2 * bqf A B C l w := by unfold bqf; ring
  rw [key, hlin, hquad, ← hmF, taylor_identity R u (Q.eval x), hm, hr]
  ring

/-- **Proposition 4.1.** Assume (20) `Δ = B² - 4AC ≠ 0` and (21) `m = R(u) = F(p, q) ≠ 0`,
let `r = R'(u)` and let `D_u` be defined in (6). If there are infinitely many integer
pairs `(x, v)` satisfying (26) `4 m D_u(Q(x)) - r² = -Δ v²` and the congruences (27)
`rp + v(Bp + 2Cq) ≡ 0`, `rq - v(2Ap + Bq) ≡ 0 (mod 2|m|)`, then `F(y, z) = R(Q(x))` is
solvable in integers `(y, z)` for infinitely many integers `x`. -/
theorem proposition_4_1 (A B C : ℤ) (hΔ : B ^ 2 - 4 * A * C ≠ 0) (R Q : ℤ[X]) (u p q m r : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (hinf : {xv : ℤ × ℤ | 4 * m * (Du R u).eval (Q.eval xv.1) - r ^ 2 =
        -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
      2 * |m| ∣ r * p + xv.2 * (B * p + 2 * C * q) ∧
      2 * |m| ∣ r * q - xv.2 * (2 * A * p + B * q)}.Infinite) :
    {x : ℤ | ∃ y z : ℤ, bqf A B C y z = R.eval (Q.eval x)}.Infinite := by
  have hX := infinite_fst_of_sq hinf (-(B ^ 2 - 4 * A * C))
    (fun x => 4 * m * (Du R u).eval (Q.eval x) - r ^ 2) (neg_ne_zero.mpr hΔ)
    (fun xv h => h.1.symm)
  apply hX.mono
  rintro _ ⟨⟨x, v⟩, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨_, _, proposition_4_1_recovery A B C R Q u p q m r hm hmF hm0 hr x v h1 h2 h3⟩

/-- **Proposition 4.2.** Let `Δ = B² - 4AC`, `m ≠ 0`, and consider equation (29)
`a x² + b x + c = -Δ v²` together with the congruences (27). Assume that
(a) either `a = 0` or `-aΔ` is a positive integer that is not a perfect square,
(b) `b² - 4ac ≠ 0`, and (c) (29) has an integer solution `(x₀, v₀)` satisfying (27).
Then (29) has infinitely many integer solutions `(x, v)` satisfying (27).

(In the paper `m = R(u) = F(p, q)` and `r = R'(u)`; only `m ≠ 0` is needed here. The paper
invokes Gauss's theorem [11, Proposition 3.14] for the case `a ≠ 0`; here that case is
proved from `pell_orbit_infinite`.) -/
theorem proposition_4_2 (A B C p q r m a b c : ℤ) (hm : m ≠ 0)
    (ha : a = 0 ∨ (0 < -a * (B ^ 2 - 4 * A * C) ∧ ¬ IsSquare (-a * (B ^ 2 - 4 * A * C))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = -(B ^ 2 - 4 * A * C) * v0 ^ 2 ∧
      2 * |m| ∣ r * p + v0 * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v0 * (2 * A * p + B * q)) :
    {xv : ℤ × ℤ | a * xv.1 ^ 2 + b * xv.1 + c = -(B ^ 2 - 4 * A * C) * xv.2 ^ 2 ∧
      2 * |m| ∣ r * p + xv.2 * (B * p + 2 * C * q) ∧
      2 * |m| ∣ r * q - xv.2 * (2 * A * p + B * q)}.Infinite := by
  obtain ⟨x0, v0, h0, hc1, hc2⟩ := hc
  set Δ := B ^ 2 - 4 * A * C with hΔdef
  have h2m : 2 * |m| ∣ 2 * m := by
    rw [show 2 * |m| = |2 * m| by rw [abs_mul, abs_two], abs_dvd]
  -- congruences are preserved when `v ≡ v₀ (mod 2m)`
  have hcong : ∀ v : ℤ, 2 * m ∣ v - v0 →
      2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v * (2 * A * p + B * q) := by
    intro v hv
    have hv' := h2m.trans hv
    constructor
    · have := hc1.add (hv'.mul_right (B * p + 2 * C * q)); ring_nf at this ⊢; exact this
    · have := hc2.sub (hv'.mul_right (2 * A * p + B * q)); ring_nf at this ⊢; exact this
  rcases ha with rfl | ⟨ha, hsq⟩
  · have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    let f : ℤ → ℤ × ℤ := fun k =>
      (x0 - Δ * (4 * m * k * v0 + 4 * m ^ 2 * b * k ^ 2), v0 + 2 * m * b * k)
    have hf : Function.Injective f := by
      intro k l hkl
      have := congrArg Prod.snd hkl
      simp only [f] at this
      have h' : (2 * m * b) * k = (2 * m * b) * l := by linarith
      exact mul_left_cancel₀ (by positivity) h'
    apply (Set.infinite_range_of_injective hf).mono
    rintro _ ⟨k, rfl⟩
    refine ⟨?_, hcong _ ⟨b * k, by ring⟩⟩
    simp only [f]
    linear_combination h0
  · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hsq4 : ¬ IsSquare (4 * (-a * Δ)) := fun h => hsq (isSquare_of_isSquare_four_mul h)
    have hN : 2 * a * (2 * m) ≠ 0 := by positivity
    have hP := pell_orbit_infinite (4 * (-a * Δ)) (b ^ 2 - 4 * a * c) (2 * a * (2 * m))
      (2 * a * x0 + b) v0 (by positivity) hsq4 hN (by linear_combination 4 * a * h0) hb
    let φ : ℤ × ℤ → ℤ × ℤ := fun XV => ((XV.1 - b) / (2 * a), XV.2)
    have hrec : ∀ XV ∈ {XV : ℤ × ℤ | XV.1 ^ 2 - 4 * (-a * Δ) * XV.2 ^ 2 = b ^ 2 - 4 * a * c ∧
        2 * a * (2 * m) ∣ XV.1 - (2 * a * x0 + b) ∧ 2 * a * (2 * m) ∣ XV.2 - v0},
        XV.1 = 2 * a * (φ XV).1 + b := by
      rintro ⟨X, V⟩ ⟨_, h2, _⟩
      have : 2 * a ∣ X - b := by
        have := (dvd_mul_right (2 * a) (2 * m)).trans h2
        have := this.add (dvd_mul_right (2 * a) x0); ring_nf at this ⊢; exact this
      simp only [φ]
      rw [Int.mul_ediv_cancel' this]; ring
    apply (hP.image (f := φ) ?_).mono
    · rintro _ ⟨⟨X, V⟩, hXV, rfl⟩
      have hX := hrec _ hXV
      obtain ⟨h1, -, h3⟩ := hXV
      refine ⟨?_, hcong V ((dvd_mul_left (2 * m) (2 * a)).trans h3)⟩
      simp only at hX h1
      rw [hX] at h1
      have : 4 * a * (a * (φ (X, V)).1 ^ 2 + b * (φ (X, V)).1 + c + Δ * V ^ 2) = 0 := by
        linear_combination h1
      have := (mul_eq_zero.mp this).resolve_left (by positivity)
      simp only [φ] at this ⊢
      linarith
    · intro p hp q hq hpq
      have e1 := hrec p hp
      have e2 := hrec q hq
      rw [hpq] at e1
      exact Prod.ext (by rw [e1, e2]) (by simpa [φ] using congrArg Prod.snd hpq)

/-- **Algorithm 4.1, Step 2.** For admissible `(deg R, deg Q)`, the auxiliary equation (26)
`4 m D_u(Q(x)) - r² = -Δ v²` can be written in the form (29) `a x² + b x + c = -Δ v²`. -/
theorem algorithm_4_1_step2 (R Q : ℤ[X]) (hdeg : AdmissibleDegrees R Q) (u m r : ℤ) :
    ∃ a b c : ℤ, ∀ x : ℤ, 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = a * x ^ 2 + b * x + c :=
  aux_equation_quadratic R Q hdeg u _ _

/-- **Algorithm 4.1 (correctness of the output).** Let `F = A y² + B y z + C z²` be
non-degenerate. If Step 1 finds `u, p, q` with `m = R(u) = F(p, q) ≠ 0`, Step 2 writes (26)
as (29) `a x² + b x + c = -Δ v²` (with `r = R'(u)`), and conditions (a)–(c) of
Proposition 4.2 hold (so that the algorithm stops), then `F(y, z) = R(Q(x))` is solvable in
integers `(y, z)` for infinitely many integers `x`.

(The degree restriction on `(R, Q)` only serves to guarantee that Step 2 is possible, see
`algorithm_4_1_step2`; it is not needed for this implication.) -/
theorem algorithm_4_1 (A B C : ℤ) (hΔ : B ^ 2 - 4 * A * C ≠ 0) (R Q : ℤ[X])
    (u p q m r a b c : ℤ)
    (hm : R.eval u = m) (hmF : m = bqf A B C p q) (hm0 : m ≠ 0) (hr : R.derivative.eval u = r)
    (habc : ∀ x : ℤ, 4 * m * (Du R u).eval (Q.eval x) - r ^ 2 = a * x ^ 2 + b * x + c)
    (ha : a = 0 ∨ (0 < -a * (B ^ 2 - 4 * A * C) ∧ ¬ IsSquare (-a * (B ^ 2 - 4 * A * C))))
    (hb : b ^ 2 - 4 * a * c ≠ 0)
    (hc : ∃ x0 v0 : ℤ, a * x0 ^ 2 + b * x0 + c = -(B ^ 2 - 4 * A * C) * v0 ^ 2 ∧
      2 * |m| ∣ r * p + v0 * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v0 * (2 * A * p + B * q)) :
    {x : ℤ | ∃ y z : ℤ, bqf A B C y z = R.eval (Q.eval x)}.Infinite := by
  refine proposition_4_1 A B C hΔ R Q u p q m r hm hmF hm0 hr ?_
  convert proposition_4_2 A B C p q r m a b c hm0 ha hb hc using 1
  ext xv
  simp only [mem_setOf_iff', habc]

/-- **Seed test for Algorithm 4.1 in the linear case `a = 0`** (Section 4): if `b ≠ 0` and
`m ≠ 0`, then `b x + c = -Δ v²` has an integer solution satisfying the congruences (27) iff
some `v` with `0 ≤ v < lcm(2|m|, |b|)` satisfies (27) and `b ∣ -Δ v² - c`; then
`x = (-Δ v² - c)/b`. -/
theorem algorithm_4_1_linear_seed_test (A B C p q r m b c : ℤ) (hm : m ≠ 0) (hb : b ≠ 0) :
    (∃ x v : ℤ, b * x + c = -(B ^ 2 - 4 * A * C) * v ^ 2 ∧
      2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v * (2 * A * p + B * q)) ↔
    ∃ v : ℤ, 0 ≤ v ∧ v < (Int.lcm (2 * m) b : ℤ) ∧
      2 * |m| ∣ r * p + v * (B * p + 2 * C * q) ∧ 2 * |m| ∣ r * q - v * (2 * A * p + B * q) ∧
      b ∣ -(B ^ 2 - 4 * A * C) * v ^ 2 - c := by
  set Δ := B ^ 2 - 4 * A * C
  constructor
  · rintro ⟨x, v, h, hc1, hc2⟩
    set L : ℤ := (Int.lcm (2 * m) b : ℤ)
    have hL : 0 < L := by
      exact Int.natCast_pos.mpr (Int.lcm_pos (mul_ne_zero two_ne_zero hm) hb)
    have hvL : L ∣ v - v % L := ((Int.mod_modEq v L).dvd)
    have h2m : 2 * |m| ∣ L := by
      rw [show 2 * |m| = |2 * m| by rw [abs_mul, abs_two], abs_dvd]
      exact Int.dvd_lcm_left _ _
    have hbL : b ∣ L := Int.dvd_lcm_right _ _
    refine ⟨v % L, Int.emod_nonneg v hL.ne', Int.emod_lt_of_pos v hL, ?_, ?_, ?_⟩
    · have := hc1.sub ((h2m.trans hvL).mul_right (B * p + 2 * C * q))
      ring_nf at this ⊢; exact this
    · have := hc2.add ((h2m.trans hvL).mul_right (2 * A * p + B * q))
      ring_nf at this ⊢; exact this
    · have h1 : b ∣ -Δ * v ^ 2 - c := ⟨x, by linarith⟩
      have h2 : b ∣ Δ * (v + v % L) * (v - v % L) := (hbL.trans hvL).mul_left _
      have := h1.add h2
      ring_nf at this ⊢; exact this
  · rintro ⟨v, -, -, hc1, hc2, x, hx⟩
    exact ⟨x, v, by linarith, hc1, hc2⟩

/-- **Proposition 4.3.** Both equations (31) `2y² + yz + 2z² = x³ + 1` and
`2y² + yz + 2z² = x³ - 1` have infinitely many integer solutions; explicitly, for every
`n ∈ ℤ` the recovery formulas give the families
`(x, y, z) = (30n² + 15n + 1, 30n³ + 45n² + 15n + 1, -120n³ - 90n² - 15n)` for (a) and
`(x, y, z) = (570n² + 225n + 24, 9690n³ + 6105n² + 1189n + 71, -4560n³ - 1230n² + 89n + 29)`
for (b). -/
theorem proposition_4_3_families (n : ℤ) :
    bqf 2 1 2 (30 * n ^ 3 + 45 * n ^ 2 + 15 * n + 1) (-120 * n ^ 3 - 90 * n ^ 2 - 15 * n) =
      (30 * n ^ 2 + 15 * n + 1) ^ 3 + 1 ∧
    bqf 2 1 2 (9690 * n ^ 3 + 6105 * n ^ 2 + 1189 * n + 71)
      (-4560 * n ^ 3 - 1230 * n ^ 2 + 89 * n + 29) = (570 * n ^ 2 + 225 * n + 24) ^ 3 - 1 := by
  unfold bqf; constructor <;> ring

/-- **Proposition 4.3.** Both equations (31) have infinitely many integer solutions. -/
theorem proposition_4_3 :
    {s : ℤ × ℤ × ℤ | bqf 2 1 2 s.2.1 s.2.2 = s.1 ^ 3 + 1}.Infinite ∧
      {s : ℤ × ℤ × ℤ | bqf 2 1 2 s.2.1 s.2.2 = s.1 ^ 3 - 1}.Infinite := by
  constructor
  · let f : ℕ → ℤ × ℤ × ℤ := fun n => (30 * (n : ℤ) ^ 2 + 15 * n + 1,
      30 * (n : ℤ) ^ 3 + 45 * n ^ 2 + 15 * n + 1, -120 * (n : ℤ) ^ 3 - 90 * n ^ 2 - 15 * n)
    have hf : Function.Injective f := by
      intro k l h
      have h1 := congrArg Prod.fst h
      simp only [f] at h1
      have : (k : ℤ) = l := by
        rcases lt_trichotomy (k : ℤ) l with hkl | hkl | hkl
        · have : (0 : ℤ) ≤ k := by positivity
          nlinarith
        · exact hkl
        · have : (0 : ℤ) ≤ l := by positivity
          nlinarith
      exact_mod_cast this
    exact (Set.infinite_range_of_injective hf).mono (by
      rintro _ ⟨n, rfl⟩; exact (proposition_4_3_families n).1)
  · let f : ℕ → ℤ × ℤ × ℤ := fun n => (570 * (n : ℤ) ^ 2 + 225 * n + 24,
      9690 * (n : ℤ) ^ 3 + 6105 * n ^ 2 + 1189 * n + 71,
      -4560 * (n : ℤ) ^ 3 - 1230 * n ^ 2 + 89 * n + 29)
    have hf : Function.Injective f := by
      intro k l h
      have h1 := congrArg Prod.fst h
      simp only [f] at h1
      have : (k : ℤ) = l := by
        rcases lt_trichotomy (k : ℤ) l with hkl | hkl | hkl
        · have : (0 : ℤ) ≤ k := by positivity
          nlinarith
        · exact hkl
        · have : (0 : ℤ) ≤ l := by positivity
          nlinarith
      exact_mod_cast this
    exact (Set.infinite_range_of_injective hf).mono (by
      rintro _ ⟨n, rfl⟩; exact (proposition_4_3_families n).2)

/-- The data used in the proof of Proposition 4.3, checked against Algorithm 4.1:
for (a), `R(t) = t³ + 1`, `u = 1`, `(p, q) = (1, 0)`, `m = 2 = F(1, 0)`, `r = 3`,
`D_u(t) = t + 2`, and (26) reads `8x + 7 = 15v²`; for (b), `R(t) = t³ - 1`, `u = 7`,
`(p, q) = (3, 12)`, `m = 342 = F(3, 12)`, `r = 147`, `D_u(t) = t + 14`, and (26) reads
`456x - 819 = 5v²`. Here `Δ = 1 - 16 = -15`. -/
theorem proposition_4_3_data (x v : ℤ) :
    (bqf 2 1 2 1 0 = (X ^ 3 + C 1 : ℤ[X]).eval 1 ∧
      (X ^ 3 + C 1 : ℤ[X]).derivative.eval 1 = 3 ∧ Du (X ^ 3 + C 1) 1 = X + C 2 ∧
      (4 * 2 * (Du (X ^ 3 + C 1) 1).eval x - 3 ^ 2 = -((1 : ℤ) ^ 2 - 4 * 2 * 2) * v ^ 2 ↔
        8 * x + 7 = 15 * v ^ 2)) ∧
    (bqf 2 1 2 3 12 = (X ^ 3 + C (-1) : ℤ[X]).eval 7 ∧
      (X ^ 3 + C (-1) : ℤ[X]).derivative.eval 7 = 147 ∧
      Du (X ^ 3 + C (-1)) 7 = X + C 14 ∧
      (4 * 342 * (Du (X ^ 3 + C (-1)) 7).eval x - 147 ^ 2 =
          -((1 : ℤ) ^ 2 - 4 * 2 * 2) * v ^ 2 ↔ 456 * x - 819 = 5 * v ^ 2)) := by
  refine ⟨⟨by simp [bqf], by simp, by rw [Du_cubic]; norm_num, ?_⟩,
    ⟨by simp [bqf], by norm_num, by rw [Du_cubic]; norm_num, ?_⟩⟩
  · rw [Du_cubic]; simp only [eval_add, eval_X, eval_C]; constructor <;> intro h <;> linarith
  · rw [Du_cubic]; simp only [eval_add, eval_X, eval_C]
    constructor <;> intro h <;> linarith

lemma sq_mod_three_ne_two (s : ℤ) : s ^ 2 % 3 ≠ 2 := by
  have h : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- The non-multiplicative form `F(y, z) = 2y² + yz + 2z²` of Section 4: it represents `2`
(as `F(0, 1)`), but does not represent `2 · 2 = 4`. -/
theorem non_multiplicative_example :
    bqf 2 1 2 0 1 = 2 ∧ ∀ y z : ℤ, bqf 2 1 2 y z ≠ 4 := by
  refine ⟨by simp [bqf], fun y z h => ?_⟩
  unfold bqf at h
  have e : (y + z) ^ 2 = 3 * (y ^ 2 + y * z + z ^ 2 - 2) + 2 := by linear_combination -h
  exact sq_mod_three_ne_two (y + z) (by omega)

/-- The remark at the end of Section 4: the form `4(y² + z²)` is multiplicative (if it
represents positive integers `m` and `n`, it represents `mn`) and represents `4 = 4 · 1`,
but it does not represent `1`; so multiplicativity alone does not give the cancellation
direction of property (*). -/
theorem four_sum_two_squares_remark :
    (∀ m n : ℤ, (∃ y z : ℤ, m = 4 * (y ^ 2 + z ^ 2)) → (∃ y z : ℤ, n = 4 * (y ^ 2 + z ^ 2)) →
      ∃ y z : ℤ, m * n = 4 * (y ^ 2 + z ^ 2)) ∧
    (∃ y z : ℤ, (4 : ℤ) = 4 * (y ^ 2 + z ^ 2)) ∧ (∀ y z : ℤ, (1 : ℤ) ≠ 4 * (y ^ 2 + z ^ 2)) := by
  refine ⟨?_, ⟨1, 0, by norm_num⟩, fun y z h => by omega⟩
  rintro m n ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
  exact ⟨2 * (a * c - b * d), 2 * (a * d + b * c), by ring⟩

/-- **Degenerate case, parametrisation.** If `B² - 4AC = 0`, then
`(A, B, C) = (k r², 2 k r s, k s²)` for some integers `k, r, s`. -/
theorem degenerate_parametrisation (A B C : ℤ) (h : B ^ 2 - 4 * A * C = 0) :
    ∃ k r s : ℤ, A = k * r ^ 2 ∧ B = 2 * k * r * s ∧ C = k * s ^ 2 := by
  obtain ⟨B', rfl⟩ : Even B := by
    by_contra hB
    rw [Int.not_even_iff_odd] at hB
    obtain ⟨t, rfl⟩ := hB
    have : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring
    have h' : 4 * (t ^ 2 + t) + 1 = 4 * (A * C) := by linarith
    generalize A * C = M at h'
    generalize t ^ 2 + t = T at h'
    omega
  have hB' : B' ^ 2 = A * C := by
    have : 4 * (B' ^ 2 - A * C) = 0 := by linear_combination h
    linarith
  by_cases hA : A = 0
  · subst hA
    have : B' = 0 := by simpa using hB'
    subst this
    exact ⟨C, 0, 1, by ring, by ring, by ring⟩
  · have hg : 0 < Int.gcd A B' := Int.gcd_pos_of_ne_zero_left _ hA
    set g : ℤ := (Int.gcd A B' : ℤ) with hgdef
    have hg0 : g ≠ 0 := by positivity
    obtain ⟨r, hr⟩ : g ∣ A := Int.gcd_dvd_left _ _
    obtain ⟨s, hs⟩ : g ∣ B' := Int.gcd_dvd_right _ _
    have hcop : IsCoprime r s := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := Int.gcd_div_gcd_div_gcd hg
      rw [← hgdef, hr, hs, Int.mul_ediv_cancel_left _ hg0, Int.mul_ediv_cancel_left _ hg0] at this
      exact this
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hA hr
    have e : g * s ^ 2 = r * C := by
      apply mul_left_cancel₀ hg0
      have h2 : (g * s) ^ 2 = g * r * C := by rw [← hs, ← hr]; exact hB'
      linear_combination h2
    obtain ⟨k, hk⟩ : r ∣ g := (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right ⟨C, e⟩
    refine ⟨k, r, s, ?_, ?_, ?_⟩
    · rw [hr, hk]; ring
    · rw [hs, hk]; ring
    · apply mul_left_cancel₀ hr0
      rw [← e, hk]; ring

/-- In the degenerate case `F(y, z) = k (r y + s z)²`. -/
theorem degenerate_form_eq (k r s y z : ℤ) :
    bqf (k * r ^ 2) (2 * k * r * s) (k * s ^ 2) y z = k * (r * y + s * z) ^ 2 := by
  unfold bqf; ring

/-- **Degenerate case, "if and only if".** Suppose `(A, B, C) = (k r², 2 k r s, k s²)`.
Then the equation `F(y, z) = P(x)` has infinitely many integer solutions `(x, y, z)` if and
only if equation (32) `k t² = P(x)` has a solution `(x₀, t₀)` with `gcd(r, s) ∣ t₀`.
(This holds for every such representation, including the trivial case
`(A, B, C) = (0, 0, 0)`.) -/
theorem degenerate_infinite_iff (A B C k r s : ℤ) (hA : A = k * r ^ 2) (hB : B = 2 * k * r * s)
    (hC : C = k * s ^ 2) (P : ℤ[X]) :
    {t : ℤ × ℤ × ℤ | bqf A B C t.2.1 t.2.2 = P.eval t.1}.Infinite ↔
      ∃ x0 t0 : ℤ, k * t0 ^ 2 = P.eval x0 ∧ (Int.gcd r s : ℤ) ∣ t0 := by
  subst hA hB hC
  simp only [degenerate_form_eq]
  constructor
  · intro h
    obtain ⟨⟨x, y, z⟩, hxyz⟩ := h.nonempty
    exact ⟨x, r * y + s * z, hxyz,
      dvd_add ((Int.gcd_dvd_left r s).mul_right y) ((Int.gcd_dvd_right r s).mul_right z)⟩
  · rintro ⟨x0, t0, h, c, rfl⟩
    by_cases hrs : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := hrs
      let f : ℤ → ℤ × ℤ × ℤ := fun n => (x0, n, 0)
      have hf : Function.Injective f := fun a b hab => by
        simpa [f] using congrArg (fun t => t.2.1) hab
      apply (Set.infinite_range_of_injective hf).mono
      rintro _ ⟨n, rfl⟩
      simpa [f] using h
    · set y0 := c * Int.gcdA r s
      set z0 := c * Int.gcdB r s
      have hb : r * y0 + s * z0 = (Int.gcd r s : ℤ) * c := by
        rw [Int.gcd_eq_gcd_ab r s]; ring
      let f : ℤ → ℤ × ℤ × ℤ := fun n => (x0, y0 + s * n, z0 - r * n)
      have hf : Function.Injective f := by
        intro a b hab
        have h1 : s * a = s * b := by
          have := congrArg (fun t => t.2.1) hab; simp only [f] at this; linarith
        have h2 : r * a = r * b := by
          have := congrArg (fun t => t.2.2) hab; simp only [f] at this; linarith
        by_cases hs : s = 0
        · have hr : r ≠ 0 := fun hr => hrs ⟨hr, hs⟩
          exact mul_left_cancel₀ hr h2
        · exact mul_left_cancel₀ hs h1
      apply (Set.infinite_range_of_injective hf).mono
      rintro _ ⟨n, rfl⟩
      show k * (r * (y0 + s * n) + s * (z0 - r * n)) ^ 2 = P.eval x0
      rw [← h, ← hb]; ring

/-- Comparison with Section 2: for `F(y, z) = y² + z²` one has `Δ = -4`, and (26) becomes
`4 m D - r² = 4 v²`, i.e. (8) with `V = 2v`; conversely, every integer solution `V` of
`4 m D - r² = V²` is even (reduction modulo 4). -/
theorem comparison_with_section_2 (m r D : ℤ) :
    ((0 : ℤ) ^ 2 - 4 * 1 * 1 = -4) ∧
    (∀ v : ℤ, 4 * m * D - r ^ 2 = -((0 : ℤ) ^ 2 - 4 * 1 * 1) * v ^ 2 ↔
      4 * m * D - r ^ 2 = (2 * v) ^ 2) ∧
    (∀ V : ℤ, 4 * m * D - r ^ 2 = V ^ 2 → Even V) := by
  refine ⟨by norm_num, fun v => by constructor <;> intro h <;> linarith, fun V h => ?_⟩
  have e : V ^ 2 + r ^ 2 = 4 * (m * D) := by linarith
  exact (sq_add_sq_even_of_mod_four_zero e (by omega)).1

end PolyQF
