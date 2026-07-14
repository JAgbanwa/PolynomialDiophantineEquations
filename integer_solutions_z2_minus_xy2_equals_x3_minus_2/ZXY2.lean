import Mathlib
/-!
# Definitions for the classification of integer solutions of `z² - x y² = x³ - 2`
This file sets up the definitions used in the paper
*"Integer solutions of z² − xy² = x³ − 2"*.
The equation `(1.1)` is `z² - x*y² = x³ - 2`, equivalently `(1.2)` `z² + 2 = x*(x² + y²)`.
-/
namespace ZXY2
open scoped Classical
/-- The Diophantine equation `(1.1)`: `z² - x·y² = x³ - 2`. -/
def IsSol (x y z : ℤ) : Prop := z ^ 2 - x * y ^ 2 = x ^ 3 - 2
/-- The set `A` of admissible positive integers `(1.3)`: `x` is a positive odd integer with
`x ≢ 2 (mod 3)`, all of whose prime divisors are `≡ 1` or `3 (mod 8)`. -/
def Admissible (x : ℤ) : Prop :=
  0 < x ∧ Odd x ∧ x % 3 ≠ 2 ∧
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → p % 8 = 1 ∨ p % 8 = 3
/-! ## Square fibers -/
/-- `M_m = m⁶ - 2`, `(1.4)`. -/
def Mm (m : ℤ) : ℤ := m ^ 6 - 2
/-- The finite set `F_m`, `(1.5)`: positive divisors `a` of `M_m` with `a ≤ M_m/a` and
`M_m/a ≡ a (mod 2m)`. -/
def Fm (m : ℤ) : Set ℤ :=
  {a | 0 < a ∧ a ∣ Mm m ∧ a ≤ Mm m / a ∧ (Mm m / a) % (2 * m) = a % (2 * m)}
/-- `Y_{m,a} = (M_m/a - a)/(2m)`, `(1.6)`. -/
def Ym (m a : ℤ) : ℤ := (Mm m / a - a) / (2 * m)
/-- `Z_{m,a} = (M_m/a + a)/2`, `(1.6)`. -/
def Zm (m a : ℤ) : ℤ := (Mm m / a + a) / 2
/-! ## Pell machinery and nonsquare fibers -/
/-- The fundamental solution of `u² - x v² = 1` (Mathlib's fundamental Pell solution),
for positive nonsquare `x`. For other `x` we return the trivial solution `(1,0)`. -/
noncomputable def fundSol (x : ℤ) : Pell.Solution₁ x :=
  if h : 0 < x ∧ ¬ IsSquare x then
    Classical.choose (Pell.IsFundamental.exists_of_not_isSquare h.1 h.2)
  else 1
/-- `u_x`: the `x`-component of the least positive Pell unit `ε_x = u_x + v_x √x`, `(1.8)`. -/
noncomputable def ux (x : ℤ) : ℤ := (fundSol x).x
/-- `v_x`: the `y`-component of the least positive Pell unit `ε_x = u_x + v_x √x`, `(1.8)`. -/
noncomputable def vx (x : ℤ) : ℤ := (fundSol x).y
/-- `N_x = x³ - 2`, `(1.9)`. -/
def Nx (x : ℤ) : ℤ := x ^ 3 - 2
/-- The reduced seed set `S_x`, `(1.10)`: pairs `(r,s)` with `r > 0`, `s ≥ 0`,
`r² - x s² = N_x` and `s² < v_x² N_x`. -/
noncomputable def Sx (x : ℤ) : Set (ℤ × ℤ) :=
  {p | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - x * p.2 ^ 2 = Nx x ∧ p.2 ^ 2 < (vx x) ^ 2 * Nx x}
/-- One step of the Pell recurrence `(1.12)`:
`(Z, Y) ↦ (u_x Z + x v_x Y, v_x Z + u_x Y)`. -/
def pellStep (x u v : ℤ) : ℤ × ℤ → ℤ × ℤ :=
  fun p => (u * p.1 + x * v * p.2, v * p.1 + u * p.2)
/-- The iterated Pell recurrence starting from the seed `(r, s)`. -/
def pellIter (x u v r s : ℤ) : ℕ → ℤ × ℤ
  | 0 => (r, s)
  | (n + 1) => pellStep x u v (pellIter x u v r s n)
/-- `Z_n(x; r, s)`, `(1.11)`/`(1.12)`. -/
noncomputable def Zseq (x r s : ℤ) (n : ℕ) : ℤ := (pellIter x (ux x) (vx x) r s n).1
/-- `Y_n(x; r, s)`, `(1.11)`/`(1.12)`. -/
noncomputable def Yseq (x r s : ℤ) (n : ℕ) : ℤ := (pellIter x (ux x) (vx x) r s n).2
end ZXY2
/-!
# Section 2: Local restrictions on `x`
We prove Lemma 2.1 (the residue class of primes representing `-2`) and
Proposition 2.2 (necessary conditions on `x`).
-/
namespace ZXY2
open scoped Classical
/--
**Lemma 2.1.** For an odd prime `p`, the congruence `t² ≡ -2 (mod p)` is solvable iff
`p ≡ 1` or `3 (mod 8)`.
-/
theorem lemma21 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ t : ZMod p, t ^ 2 = -2) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  exact ⟨ fun ⟨ t, ht ⟩ ↦ by have := ZMod.exists_sq_eq_neg_two_iff hp; exact this.mp ( by exact ⟨ t, by simpa only [ sq ] using ht.symm ⟩ ), fun h ↦ by have := ZMod.exists_sq_eq_neg_two_iff hp; exact this.mpr h |> fun ⟨ t, ht ⟩ ↦ ⟨ t, by simpa only [ sq ] using ht.symm ⟩ ⟩
/--
Multiplicativity of the residue condition: a positive integer all of whose prime
divisors are `≡ 1` or `3 (mod 8)` is itself `≡ 1` or `3 (mod 8)`. (`{1,3}` is closed under
multiplication mod `8`; oddness is automatic since `2 ∉ {1,3} (mod 8)`.)
-/
theorem prod_primes_mod8 (n : ℤ) (hn : 0 < n)
    (hp : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → p % 8 = 1 ∨ p % 8 = 3) :
    n % 8 = 1 ∨ n % 8 = 3 := by
  -- By induction on the number of prime factors of $n$, we can show that $n \equiv 1 \pmod{8}$ or $n \equiv 3 \pmod{8}$.
  have h_ind : ∀ {k : ℕ}, (∀ p : ℕ, Nat.Prime p → p ∣ k → p % 8 = 1 ∨ p % 8 = 3) → k % 8 = 1 ∨ k % 8 = 3 := by
    intro k hk; induction' k using Nat.strongRecOn with k ih; rcases k with ( _ | _ | k ) <;> simp_all +decide ;
    · exact absurd ( hk 2 Nat.prime_two ) ( by decide );
    · obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_and_dvd ( by linarith : k + 1 + 1 ≠ 1 );
      obtain ⟨ q, hq ⟩ := hp₂; simp_all +decide ;
      rcases ih q ( by nlinarith [ hp₁.two_le ] ) ( fun r hr hr' => hk r hr ( dvd_mul_of_dvd_right hr' _ ) ) with ha | ha <;> rcases hk p hp₁ ( dvd_mul_right _ _ ) with hb | hb <;> norm_num [ Nat.mul_mod, ha, hb ];
  convert h_ind fun p pp dp => hp p pp <| Int.natCast_dvd.mpr dp; all_goals omega
/-- Equation `(1.2)`: `z² + 2 = x·(x² + y²)` is equivalent to `IsSol`. -/
theorem isSol_iff (x y z : ℤ) : IsSol x y z ↔ z ^ 2 + 2 = x * (x ^ 2 + y ^ 2) := by
  unfold IsSol; constructor <;> intro h <;> ring_nf <;> ring_nf at h <;> linarith
/-- From `(1.2)`, `x > 0`. -/
theorem sol_x_pos {x y z : ℤ} (h : IsSol x y z) : 0 < x := by
  nlinarith [ sq_nonneg ( x^2 ), sq_nonneg ( y^2 ), sq_nonneg ( z^2 ), isSol_iff x y z |>.1 h ]
/-- Every odd prime divisor of `x` is `≡ 1` or `3 (mod 8)`. -/
theorem sol_prime_div {x y z : ℤ} (h : IsSol x y z) (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hdvd : (p : ℤ) ∣ x) : p % 8 = 1 ∨ p % 8 = 3 := by
  have h_cong : (z : ZMod p) ^ 2 = -2 := by
    obtain ⟨ k, hk ⟩ := hdvd; replace h := congr_arg ( ( ↑ ) : ℤ → ZMod p ) h; simp_all +decide [ sq, mul_assoc ] ;
  haveI := Fact.mk hp; exact lemma21 p hodd |>.1 ⟨ z, by simpa [ ← ZMod.intCast_eq_intCast_iff ] using h_cong ⟩ ;
/--
`x` is odd.
-/
theorem sol_x_odd {x y z : ℤ} (h : IsSol x y z) : Odd x := by
  obtain ⟨ k, hk ⟩ := Int.even_or_odd' x;
  obtain rfl | rfl := hk;
  · -- Since $x$ is even, we have $z^2 + 2 = 2k(4k^2 + y^2)$. This implies that $z$ must be even, so let $z = 2w$.
    obtain ⟨w, rfl⟩ : ∃ w : ℤ, z = 2 * w := by
      exact even_iff_two_dvd.mp ( by replace h := congr_arg Even h; simp_all +decide [ parity_simps ] );
    -- Dividing both sides by 2, we get $2w^2 + 1 = k(4k^2 + y^2)$.
    have h_div : 2 * w ^ 2 + 1 = k * (4 * k ^ 2 + y ^ 2) := by
      unfold IsSol at h; linarith;
    -- Since $k$ is odd, we have $k \equiv 1 \pmod{8}$ or $k \equiv 3 \pmod{8}$.
    have hk_mod : k % 8 = 1 ∨ k % 8 = 3 := by
      have hk_mod : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ k → p % 8 = 1 ∨ p % 8 = 3 := by
        intro p pp dk;
        convert sol_prime_div h p pp ( by
          rintro rfl; replace h_div := congr_arg Even h_div; simp_all +decide [ parity_simps ] ;
          grind ) ( dvd_mul_of_dvd_right dk _ ) using 1;
      convert prod_primes_mod8 k _ hk_mod;
      nlinarith [ sq_nonneg ( k^2 ), sq_nonneg ( y^2 ) ];
    replace h_div := congr_arg ( · % 8 ) h_div ; norm_num [ Int.add_emod, Int.mul_emod, sq ] at h_div;
    have := Int.emod_nonneg w ( by decide : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg y ( by decide : ( 8 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos w ( by decide : ( 8 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 8 : ℤ ) > 0 ) ; interval_cases w % 8 <;> interval_cases y % 8 <;> rcases hk_mod with ( hk | hk ) <;> simp +decide only [hk] at h_div;
  · norm_num
/--
`x ≢ 2 (mod 3)`.
-/
theorem sol_x_not_two_mod3 {x y z : ℤ} (h : IsSol x y z) : x % 3 ≠ 2 := by
  unfold IsSol at h;
  intro hx
  have h_mod3 : (z ^ 2 + y ^ 2) % 3 = 0 := by
    replace h := congr_arg ( · % 3 ) h ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, hx ] at h ⊢ ; have := Int.emod_nonneg z three_pos.ne'; have := Int.emod_nonneg y three_pos.ne'; have := Int.emod_lt_of_pos z three_pos; have := Int.emod_lt_of_pos y three_pos; interval_cases z % 3 <;> interval_cases y % 3 <;> trivial;
  -- From `h_mod3`, we know that `3 ∣ y` and `3 ∣ z`.
  have h_div3 : 3 ∣ y ∧ 3 ∣ z := by
    norm_num [ sq, Int.add_emod, Int.mul_emod ] at h_mod3;
    rw [ Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero ] ; have := Int.emod_nonneg y three_pos.ne'; have := Int.emod_nonneg z three_pos.ne'; have := Int.emod_lt_of_pos y three_pos; have := Int.emod_lt_of_pos z three_pos; interval_cases y % 3 <;> interval_cases z % 3 <;> trivial;
  obtain ⟨ k, rfl ⟩ := h_div3.left; obtain ⟨ l, rfl ⟩ := h_div3.right; ( replace h := congr_arg ( · % 9 ) h ; ring_nf at h ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, pow_three, hx ] at h; );
  rw [ ← Int.emod_emod_of_dvd x ( by decide : ( 3 : ℤ ) ∣ 9 ) ] at hx; have := Int.emod_nonneg x ( by decide : ( 9 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos x ( by decide : ( 9 : ℤ ) > 0 ) ; interval_cases x % 9 <;> contradiction;
/-- **Proposition 2.2.** Every integer solution of `(1.1)` has `x ∈ A`. -/
theorem prop22 {x y z : ℤ} (h : IsSol x y z) : Admissible x := by
  refine ⟨sol_x_pos h, sol_x_odd h, sol_x_not_two_mod3 h, ?_⟩
  intro p hp hdvd
  rcases eq_or_ne p 2 with rfl | hp2
  · exfalso
    have hxodd := sol_x_odd h
    rw [Int.odd_iff] at hxodd
    omega
  · exact sol_prime_div h p hp hp2 hdvd
/-- **Proposition 2.2, corollary `(2.10)`.** Every admissible `x` satisfies
`x ≡ 1, 3, 9,` or `19 (mod 24)`. -/
theorem admissible_mod24 {x : ℤ} (h : Admissible x) :
    x % 24 = 1 ∨ x % 24 = 3 ∨ x % 24 = 9 ∨ x % 24 = 19 := by
  obtain ⟨hpos, _hodd, _h3, hpr⟩ := h
  have h8 : x % 8 = 1 ∨ x % 8 = 3 := prod_primes_mod8 x hpos hpr
  omega
end ZXY2
/-!
# Section 3: A finite-seed theorem for generalized Pell equations
We develop the Pell machinery: existence of positive Pell solutions (Theorem 3.2),
the least positive Pell unit (Definition 3.3), the finite-seed decomposition (Theorem 3.4)
and its corollary (Corollary 3.5).
The representation `Z + Y√D = (r + s√D) εᴰⁿ` is expressed via the integer recurrence
`pellIter` (equations `(1.12)`).
-/
namespace ZXY2
open scoped Classical
/--
**Theorem 3.2.** For every positive nonsquare integer `D` there exist positive integers
`u, v` with `u² - D v² = 1`.
-/
theorem exists_pos_pell {D : ℤ} (hD : 0 < D) (hns : ¬ IsSquare D) :
    ∃ u v : ℤ, 0 < u ∧ 0 < v ∧ u ^ 2 - D * v ^ 2 = 1 := by
  obtain ⟨ x, y, hxy ⟩ := Pell.exists_of_not_isSquare hD hns;
  exact ⟨ |x|, |y|, abs_pos.mpr ( show x ≠ 0 by rintro rfl; exact hns ⟨ 1, by nlinarith ⟩ ), abs_pos.mpr hxy.2, by simpa [ abs_mul ] using hxy.1 ⟩
/--
The chosen fundamental solution really is fundamental (for positive nonsquare `x`).
-/
theorem fund_isFundamental {x : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) :
    Pell.IsFundamental (fundSol x) := by
  unfold fundSol;
  grind +qlia
/-- The least positive Pell unit satisfies `u_x² - x v_x² = 1`. -/
theorem ux_vx_prop (x : ℤ) : (ux x) ^ 2 - x * (vx x) ^ 2 = 1 := (fundSol x).prop
/-- For positive nonsquare `x`, `1 < u_x`. -/
theorem one_lt_ux {x : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) : 1 < ux x :=
  (fund_isFundamental hx hns).1
/-- For positive nonsquare `x`, `0 < v_x`. -/
theorem vx_pos {x : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) : 0 < vx x :=
  (fund_isFundamental hx hns).2.1
/-- The generalized reduced seed set `R(D, N)` from `(3.15)`. -/
noncomputable def Rset (D N : ℤ) : Set (ℤ × ℤ) :=
  {p | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = N ∧ p.2 ^ 2 < (vx D) ^ 2 * N}
/-- `S_x` is `R(x, N_x)`. -/
theorem Sx_eq_Rset (x : ℤ) : Sx x = Rset x (Nx x) := rfl
/-- One Pell step preserves the norm `Z² - D Y²`. -/
theorem pellStep_norm (D u v Z Y : ℤ) (huv : u ^ 2 - D * v ^ 2 = 1) :
    (pellStep D u v (Z, Y)).1 ^ 2 - D * (pellStep D u v (Z, Y)).2 ^ 2 = Z ^ 2 - D * Y ^ 2 := by
  simp only [pellStep]
  have key : (u * Z + D * v * Y) ^ 2 - D * (v * Z + u * Y) ^ 2
      = (u ^ 2 - D * v ^ 2) * (Z ^ 2 - D * Y ^ 2) := by ring
  rw [key, huv, one_mul]
/--
**Converse part of Theorem 3.4.** Every iterate of a valid seed under the Pell recurrence
yields a nonnegative solution of `Z² - D Y² = N`.
-/
theorem seed_gives_sol {x N r s : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x)
    (hr : 0 < r) (hs : 0 ≤ s) (hrs : r ^ 2 - x * s ^ 2 = N) (n : ℕ) :
    0 < (pellIter x (ux x) (vx x) r s n).1 ∧ 0 ≤ (pellIter x (ux x) (vx x) r s n).2 ∧
      (pellIter x (ux x) (vx x) r s n).1 ^ 2 - x * (pellIter x (ux x) (vx x) r s n).2 ^ 2 = N := by
  induction' n with n ih <;> simp_all +decide [ pellIter ];
  refine' ⟨ _, _, _ ⟩;
  · exact add_pos_of_pos_of_nonneg ( mul_pos ( by linarith [ one_lt_ux hx hns ] ) ih.1 ) ( mul_nonneg ( mul_nonneg hx.le ( by linarith [ vx_pos hx hns ] ) ) ih.2.1 );
  · exact add_nonneg ( mul_nonneg ( show 0 ≤ vx x from le_of_lt ( vx_pos hx hns ) ) ih.1.le ) ( mul_nonneg ( show 0 ≤ ux x from le_of_lt ( by linarith [ one_lt_ux hx hns ] ) ) ih.2.1 );
  · convert pellStep_norm x ( ux x ) ( vx x ) ( pellIter x ( ux x ) ( vx x ) r s n |>.1 ) ( pellIter x ( ux x ) ( vx x ) r s n |>.2 ) ( ux_vx_prop x ) using 1;
    linarith
/--
When `D` is not a positive nonsquare, the fundamental solution is the trivial unit `1`,
so `v_D = 0`.
-/
theorem vx_eq_zero {D : ℤ} (h : ¬ (0 < D ∧ ¬ IsSquare D)) : vx D = 0 := by
  unfold vx fundSol
  rw [dif_neg h]
  rfl
/--
The reduced seed set is finite (`s` is bounded and `r` is determined by `s`).
-/
theorem Rset_finite (D N : ℤ) : (Rset D N).Finite := by
  by_cases hD : 0 < D ∧ ¬ IsSquare D
  · -- `D` is a positive nonsquare: both coordinates are bounded.
    refine Set.Finite.subset
      (Set.Finite.prod
        (Set.finite_Icc (0 : ℤ) ((vx D) ^ 2 * N + D * ((vx D) ^ 2 * N) + N))
        (Set.finite_Icc (0 : ℤ) ((vx D) ^ 2 * N + D * ((vx D) ^ 2 * N) + N))) ?_
    intro p hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    exact ⟨⟨by linarith, by nlinarith [hp1, hp2, hp3, hp4, hD.1, sq_nonneg (p.1 - 1), sq_nonneg (p.2 - 1)]⟩,
      ⟨by linarith, by nlinarith [hp1, hp2, hp3, hp4, hD.1, sq_nonneg (p.1 - 1), sq_nonneg (p.2 - 1)]⟩⟩
  · -- Otherwise `v_D = 0`, so the seed condition `s² < v_D² N = 0` is unsatisfiable.
    have hv : vx D = 0 := vx_eq_zero hD
    refine Set.finite_empty.subset (fun p hp => ?_)
    obtain ⟨_, _, _, hp4⟩ := hp
    rw [hv] at hp4
    nlinarith [sq_nonneg p.2, hp4]
/-- The inverse Pell step: `(Z, Y) ↦ (u Z - x v Y, u Y - v Z)` (multiplication by `ε⁻¹`). -/
def invStep (x u v : ℤ) : ℤ × ℤ → ℤ × ℤ :=
  fun p => (u * p.1 - x * v * p.2, u * p.2 - v * p.1)
/-- `pellStep` and `invStep` are inverse to each other (when `u² - x v² = 1`). -/
theorem pellStep_invStep (x u v Z Y : ℤ) (huv : u ^ 2 - x * v ^ 2 = 1) :
    pellStep x u v (invStep x u v (Z, Y)) = (Z, Y) := by
  simp only [pellStep, invStep, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · linear_combination Z * huv
  · linear_combination Y * huv
/-- The inverse Pell step preserves the norm `Z² - x Y²`. -/
theorem invStep_norm (x u v Z Y : ℤ) (huv : u ^ 2 - x * v ^ 2 = 1) :
    (u * Z - x * v * Y) ^ 2 - x * (u * Y - v * Z) ^ 2 = Z ^ 2 - x * Y ^ 2 := by
  have key : (u * Z - x * v * Y) ^ 2 - x * (u * Y - v * Z) ^ 2
      = (u ^ 2 - x * v ^ 2) * (Z ^ 2 - x * Y ^ 2) := by ring
  rw [key, huv, one_mul]
/--
**Existence part of Theorem 3.4.** Every nonnegative solution `(Z, Y)` of `Z² - x Y² = N`
arises from some reduced seed `(r, s) ∈ R(x, N)` and exponent `n`, via the Pell recurrence.
Proved by integer descent on `Y`: a non-seed solution has a strictly smaller predecessor
under `invStep`.
-/
theorem exists_seed_repr {x N : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) (hN : 0 < N)
    {Z Y : ℤ} (hZ : 0 < Z) (hY : 0 ≤ Y) (hZY : Z ^ 2 - x * Y ^ 2 = N) :
    ∃ r s, (r, s) ∈ Rset x N ∧ ∃ n : ℕ, pellIter x (ux x) (vx x) r s n = (Z, Y) := by
  induction' k : Int.toNat Y using Nat.strong_induction_on with k ih generalizing Z Y;
  by_cases hY_sq : Y ^ 2 < (vx x) ^ 2 * N;
  · exact ⟨ Z, Y, ⟨ hZ, hY, hZY, hY_sq ⟩, 0, rfl ⟩;
  · -- Set `Z' := ux x * Z - x * vx x * Y` and `Y' := ux x * Y - vx x * Z`.
    set Z' := ux x * Z - x * vx x * Y
    set Y' := ux x * Y - vx x * Z;
    -- Prove that `Z'` and `Y'` satisfy the conditions for the induction hypothesis.
    have hZ'_pos : 0 < Z' := by
      have hZ'_pos : (ux x * Z) ^ 2 > (x * vx x * Y) ^ 2 := by
        have hZ'_pos : (ux x) ^ 2 * Z ^ 2 > x ^ 2 * (vx x) ^ 2 * Y ^ 2 := by
          have hZ'_pos : (ux x) ^ 2 * Z ^ 2 = (x * (vx x) ^ 2 + 1) * Z ^ 2 := by
            exact congrArg₂ _ ( by linarith [ ux_vx_prop x ] ) rfl;
          nlinarith [ show 0 < x * vx x ^ 2 by exact mul_pos hx ( sq_pos_of_pos ( vx_pos hx hns ) ) ];
        linarith;
      nlinarith [ show 0 ≤ ux x * Z by exact mul_nonneg ( by linarith [ one_lt_ux hx hns ] ) hZ.le, show 0 ≤ x * vx x * Y by exact mul_nonneg ( mul_nonneg hx.le ( by linarith [ vx_pos hx hns ] ) ) hY ]
    have hY'_nonneg : 0 ≤ Y' := by
      simp +zetaDelta at *;
      have := ux_vx_prop x;
      nlinarith [ show 0 ≤ ux x * Y by exact mul_nonneg ( by nlinarith [ one_lt_ux hx hns ] ) hY, show 0 ≤ vx x * Z by exact mul_nonneg ( by nlinarith [ vx_pos hx hns ] ) hZ.le ]
    have hZY'_eq : Z' ^ 2 - x * Y' ^ 2 = N := by
      convert invStep_norm x ( ux x ) ( vx x ) Z Y ( ux_vx_prop x ) using 1;
      linarith
    have hY'_lt_Y : Y' < Y := by
      have hY'_lt_Y : (vx x * Z) ^ 2 - ((ux x - 1) * Y) ^ 2 > 0 := by
        have hY'_lt_Y : (vx x * Z) ^ 2 - ((ux x - 1) * Y) ^ 2 = vx x ^ 2 * N + 2 * (ux x - 1) * Y ^ 2 := by
          rw [ ← hZY ] ; ring_nf;
          rw [ show ux x ^ 2 = x * vx x ^ 2 + 1 by linarith [ ux_vx_prop x ] ] ; ring;
        exact hY'_lt_Y.symm ▸ add_pos_of_pos_of_nonneg ( mul_pos ( sq_pos_of_pos ( vx_pos hx hns ) ) hN ) ( mul_nonneg ( mul_nonneg zero_le_two ( sub_nonneg.mpr ( le_of_lt ( one_lt_ux hx hns ) ) ) ) ( sq_nonneg _ ) );
      nlinarith only [ hY'_lt_Y, show 0 ≤ vx x * Z by exact mul_nonneg ( by linarith [ vx_pos hx hns ] ) hZ.le, show 0 ≤ ( ux x - 1 ) * Y by exact mul_nonneg ( by linarith [ one_lt_ux hx hns ] ) hY ];
    specialize ih ( Int.toNat Y' ) ?_ hZ'_pos hY'_nonneg hZY'_eq rfl;
    · lia;
    · obtain ⟨ r, s, hrs, n, hn ⟩ := ih
      refine ⟨r, s, hrs, n + 1, ?_⟩
      have hstep : pellIter x (ux x) (vx x) r s (n + 1)
          = pellStep x (ux x) (vx x) (Z', Y') := by rw [pellIter, hn]
      rw [hstep]
      exact pellStep_invStep x (ux x) (vx x) Z Y (ux_vx_prop x)
/-- `invStep` undoes one `pellStep` (the other composition order). -/
theorem invStep_pellStep (x u v Z Y : ℤ) (huv : u ^ 2 - x * v ^ 2 = 1) :
    invStep x u v (pellStep x u v (Z, Y)) = (Z, Y) := by
  simp only [pellStep, invStep, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · linear_combination Z * huv
  · linear_combination Y * huv
/-- A reduced seed is not the forward image of any nonnegative solution: the predecessor of a
seed under `invStep` has a strictly negative second coordinate. This is the key fact for
uniqueness. -/
theorem seed_invStep_snd_neg {x N r s : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x)
    (hmem : (r, s) ∈ Rset x N) :
    (invStep x (ux x) (vx x) (r, s)).2 < 0 := by
  obtain ⟨hr, hs, hrs, hseed⟩ := hmem
  have hu : 1 < ux x := one_lt_ux hx hns
  have hv : 0 < vx x := vx_pos hx hns
  have hprop : (ux x) ^ 2 - x * (vx x) ^ 2 = 1 := ux_vx_prop x
  simp only [invStep]
  -- goal: ux x * s - vx x * r < 0, i.e. ux x * s < vx x * r
  nlinarith [hr, hs, hrs, hseed, hu, hv, hprop,
    mul_nonneg (le_of_lt (lt_trans one_pos hu)) hs, mul_pos hv hr,
    sq_nonneg (ux x * s - vx x * r), sq_nonneg (ux x * s + vx x * r)]
/--
Uniqueness of the seed/exponent representation: distinct reduced seeds and exponents give
distinct iterates.
-/
theorem pellIter_seed_unique {x N : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x)
    {r s r' s' : ℤ} (hm : (r, s) ∈ Rset x N) (hm' : (r', s') ∈ Rset x N) :
    ∀ {n n' : ℕ},
      pellIter x (ux x) (vx x) r s n = pellIter x (ux x) (vx x) r' s' n' →
      r = r' ∧ s = s' ∧ n = n' := by
  intros n n' h_eq
  induction' n with k hk generalizing n';
  · rcases n' with ( _ | n' ) <;> simp_all +decide [ pellIter ];
    have := seed_invStep_snd_neg hx hns hm; simp_all +decide [ pellStep, invStep ] ;
    have := ux_vx_prop x; nlinarith [ show 0 ≤ ( pellIter x ( ux x ) ( vx x ) r' s' n' ).2 from ( seed_gives_sol hx hns ( hm'.1 ) ( hm'.2.1 ) ( hm'.2.2.1 ) n' ) |>.2.1 ] ;
  · rcases n' with ( _ | n' ) <;> simp_all +decide [ pellIter ];
    · have := seed_invStep_snd_neg hx hns hm';
      have := seed_gives_sol hx hns hm.1 hm.2.1 hm.2.2.1 k;
      have := invStep_pellStep x ( ux x ) ( vx x ) ( pellIter x ( ux x ) ( vx x ) r s k |>.1 ) ( pellIter x ( ux x ) ( vx x ) r s k |>.2 ) ( ux_vx_prop x ) ; simp_all +decide [ invStep ] ;
      grind;
    · apply hk;
      convert invStep_pellStep x ( ux x ) ( vx x ) _ _ _ using 1;
      · convert congr_arg ( fun p => invStep x ( ux x ) ( vx x ) p ) h_eq using 1;
        exact Eq.symm ( invStep_pellStep x ( ux x ) ( vx x ) _ _ ( ux_vx_prop x ) );
      · exact ux_vx_prop x
/-- **Theorem 3.4 (finite-seed decomposition).** For positive nonsquare `D` and positive `N`,
every nonnegative solution `(Z, Y)` of `Z² - D Y² = N` arises uniquely from a reduced seed
`(r, s) ∈ R(D, N)` and an exponent `n`, via the Pell recurrence. -/
theorem finite_seed_repr {x N : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) (hN : 0 < N)
    {Z Y : ℤ} (hZ : 0 < Z) (hY : 0 ≤ Y) (hZY : Z ^ 2 - x * Y ^ 2 = N) :
    ∃! p : (ℤ × ℤ) × ℕ,
      p.1 ∈ Rset x N ∧ pellIter x (ux x) (vx x) p.1.1 p.1.2 p.2 = (Z, Y) := by
  obtain ⟨r, s, hmem, n, hiter⟩ := exists_seed_repr hx hns hN hZ hY hZY
  refine ⟨((r, s), n), ⟨hmem, hiter⟩, ?_⟩
  rintro ⟨⟨r', s'⟩, n'⟩ ⟨hmem', hiter'⟩
  have h := pellIter_seed_unique hx hns hmem' hmem (hiter'.trans hiter.symm)
  obtain ⟨e1, e2, e3⟩ := h
  simp only [Prod.mk.injEq]
  exact ⟨⟨e1, e2⟩, e3⟩
/--
**Corollary 3.5.** For fixed positive nonsquare `D` and positive `N`, the equation
`Z² - D Y² = N` has either no solution in `ℤ>0 × ℤ≥0` or infinitely many.
-/
theorem sol_none_or_infinite {x N : ℤ} (hx : 0 < x) (hns : ¬ IsSquare x) (hN : 0 < N) :
    (¬ ∃ Z Y : ℤ, 0 < Z ∧ 0 ≤ Y ∧ Z ^ 2 - x * Y ^ 2 = N) ∨
      {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - x * p.2 ^ 2 = N}.Infinite := by
  refine' Classical.or_iff_not_imp_left.2 fun h => _;
  -- By `exists_seed_repr`, we obtain a seed `(r, s) ∈ Rset x N` and some exponent `n`.
  obtain ⟨r, s, hr⟩ : ∃ r s, (r, s) ∈ Rset x N := by
    obtain ⟨ Z, Y, hZ, hY, hZY ⟩ := Classical.not_not.mp h; exact Exists.elim ( exists_seed_repr hx hns hN hZ hY hZY ) fun r hr => Exists.elim hr fun s hs => ⟨ r, s, hs.1 ⟩ ;
  -- By `seed_gives_sol hx hns hr.1 hr.2.1 hr.2.2.1 n`, each `f n` lies in the solution set `{p | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1^2 - x*p.2^2 = N}`.
  have h_sol : ∀ n, (pellIter x (ux x) (vx x) r s n).1 ^ 2 - x * (pellIter x (ux x) (vx x) r s n).2 ^ 2 = N ∧ 0 < (pellIter x (ux x) (vx x) r s n).1 ∧ 0 ≤ (pellIter x (ux x) (vx x) r s n).2 := by
    exact fun n => ⟨ seed_gives_sol hx hns hr.1 hr.2.1 hr.2.2.1 n |>.2.2, seed_gives_sol hx hns hr.1 hr.2.1 hr.2.2.1 n |>.1, seed_gives_sol hx hns hr.1 hr.2.1 hr.2.2.1 n |>.2.1 ⟩;
  -- The first coordinate `(f n).1` is strictly increasing in `n`: `(f (n+1)).1 = ux x * (f n).1 + x * vx x * (f n).2 ≥ ux x * (f n).1 > (f n).1` since `ux x > 1` (`one_lt_ux hx hns`), `(f n).1 > 0`, `x > 0`, `vx x > 0`, `(f n).2 ≥ 0`.
  have h_inc : StrictMono (fun n => (pellIter x (ux x) (vx x) r s n).1) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n; specialize h_sol n; simp_all +decide [ pellIter ] ;
    unfold pellStep; nlinarith [ one_lt_ux hx hns, vx_pos hx hns, mul_pos hx ( vx_pos hx hns ) ] ;
  exact Set.infinite_of_injective_forall_mem ( fun n m hnm => by simpa using h_inc.injective <| by aesop ) fun n => ⟨ h_sol n |>.2.1, h_sol n |>.2.2, h_sol n |>.1 ⟩
end ZXY2
/-!
# Section 4-5: The complete classification and examples
We assemble the complete classification (Theorem 1.1) from the fiber analyses, and record
the worked examples of Section 5.
-/
namespace ZXY2
open scoped Classical
/-- **The fiber `x = 1`, `(1.13)`.** -/
theorem fiber_x1 {y z : ℤ} : IsSol 1 y z ↔ (y = 1 ∨ y = -1) ∧ z = 0 := by
  constructor <;> intro h <;> simp_all +decide [ IsSol ];
  -- We can rewrite the equation as $(y - z)(y + z) = 1$.
  have h_factor : (y - z) * (y + z) = 1 := by
    grind;
  rw [ Int.mul_eq_one_iff_eq_one_or_neg_one ] at h_factor ; omega
/--
**Square fibers, `(1.14)`.** For `m ≥ 3`, the solutions with `x = m²` are exactly
those obtained from `a ∈ F_m` via `Y_{m,a}, Z_{m,a}` and independent signs.
(The paper assumes `m` odd, coming from `m² ∈ A`; but the congruence condition defining
`F_m` already forces the needed parity, so oddness is not required here.)
-/
theorem square_fiber {m y z : ℤ} (hm : 3 ≤ m) :
    IsSol (m ^ 2) y z ↔
      ∃ a ∈ Fm m, (y = Ym m a ∨ y = -Ym m a) ∧ (z = Zm m a ∨ z = -Zm m a) := by
  constructor;
  · intro h;
    -- Let $Z = |z|$ and $Y = |y|$. Then $Z^2 - m^2 Y^2 = Mm m$ and $Z > m Y \geq 0$.
    set Z := |z|
    set Y := |y|
    have hZ_Y : Z^2 - m^2 * Y^2 = Mm m := by
      simp +zetaDelta at *;
      unfold IsSol Mm at * ; ring_nf at * ; aesop
    have hZ_Y_pos : Z > m * Y := by
      unfold Mm at hZ_Y;
      nlinarith [ show 0 < m ^ 3 by positivity, show 0 < m ^ 4 by positivity, show 0 < m ^ 5 by positivity, show 0 < m ^ 6 by positivity, abs_nonneg z, abs_nonneg y, mul_le_mul_of_nonneg_left ( show |y| ≥ 0 by positivity ) ( show 0 ≤ m ^ 2 by positivity ) ];
    -- Let $a = Z - mY$ and $b = Z + mY$. Then $a$ and $b$ are positive integers with $a \leq b$, $a \mid Mm m$, and $b \equiv a \pmod{2m}$.
    obtain ⟨a, b, ha_pos, hb_pos, hab⟩ : ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ a ≤ b ∧ a * b = Mm m ∧ b - a = 2 * m * Y ∧ b ≡ a [ZMOD 2 * m] := by
      use Z - m * Y, Z + m * Y;
      exact ⟨ by linarith, by nlinarith [ abs_nonneg y, abs_nonneg z ], by nlinarith [ abs_nonneg y, abs_nonneg z ], by linear_combination' hZ_Y, by ring, Int.modEq_iff_dvd.mpr ⟨ -Y, by ring ⟩ ⟩;
    refine' ⟨ a, _, _, _ ⟩ <;> simp_all +decide [ Fm, Ym, Zm ];
    · rw [ ← hab.2.1, Int.mul_ediv_cancel_left _ ha_pos.ne' ];
      exact ⟨ dvd_mul_right _ _, hab.1, hab.2.2.2 ⟩;
    · rw [ ← hab.2.1, Int.mul_ediv_cancel_left _ ha_pos.ne' ];
      rw [ hab.2.2.1, Int.mul_ediv_cancel_left _ ( by positivity ) ] ; cases abs_cases y <;> first | left; linarith | right; linarith;
    · rw [ ← hab.2.1, Int.mul_ediv_cancel_left _ ha_pos.ne' ];
      exact eq_or_eq_neg_of_abs_eq ( by rw [ show ( b + a ) / 2 = Z by exact Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by nlinarith ) ] );
  · rintro ⟨ a, ⟨ ha₁, ha₂, ha₃, ha₄ ⟩, rfl | rfl, rfl | rfl ⟩ <;> unfold IsSol <;> ring_nf at *;
    · unfold Mm Ym Zm at *;
      obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp ha₄.symm;
      rw [ show ( Mm m / a + a ) / 2 = k * m + a by
            exact Int.ediv_eq_of_eq_mul_left ( by norm_num ) ( by linarith! ), show ( Mm m / a - a ) / ( 2 * m ) = k by
                                                            exact Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by rw [ show Mm m = m ^ 6 - 2 by rfl ] ; linarith ) ] ;
      nlinarith [ Int.ediv_mul_cancel ha₂ ];
    · unfold Mm Ym Zm at *;
      obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp ha₄.symm;
      rw [ show ( Mm m / a + a ) / 2 = k * m + a by
            exact Int.ediv_eq_of_eq_mul_left ( by norm_num ) ( by linarith! ), show ( Mm m / a - a ) / ( 2 * m ) = k by
                                                            exact Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by rw [ show Mm m = m ^ 6 - 2 by rfl ] ; linarith ) ] ;
      nlinarith [ Int.ediv_mul_cancel ha₂ ];
    · unfold Mm Ym Zm at *;
      obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp ha₄.symm;
      rw [ show ( Mm m / a + a ) / 2 = k * m + a by
            exact Int.ediv_eq_of_eq_mul_left ( by norm_num ) ( by linarith! ), show ( Mm m / a - a ) / ( 2 * m ) = k by
                                                            exact Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by rw [ show Mm m = m ^ 6 - 2 by rfl ] ; linarith ) ] ;
      nlinarith [ Int.ediv_mul_cancel ha₂ ];
    · unfold Mm Ym Zm at *;
      obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp ha₄.symm;
      rw [ show ( Mm m / a + a ) / 2 = k * m + a by
            exact Int.ediv_eq_of_eq_mul_left ( by norm_num ) ( by linarith! ), show ( Mm m / a - a ) / ( 2 * m ) = k by
                                                            exact Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by rw [ show Mm m = m ^ 6 - 2 by rfl ] ; linarith ) ] ;
      nlinarith [ Int.ediv_mul_cancel ha₂ ]
/--
**Square-fiber uniqueness** (part of Theorem 1.1). After normalizing to `|y|, |z|`, the
parameter `a ∈ F_m` is uniquely determined, since `a = Z_{m,a} - m·Y_{m,a}`.
-/
theorem square_fiber_unique {m a a' : ℤ} (hm : 0 < m) (ha : a ∈ Fm m) (ha' : a' ∈ Fm m)
    (hY : Ym m a = Ym m a') (hZ : Zm m a = Zm m a') : a = a' := by
  unfold Ym Zm at *;
  rw [ Int.ediv_eq_iff_eq_mul_left ( by positivity ) ] at hY;
  · rw [ Int.ediv_mul_cancel ] at hY;
    · grind +qlia;
    · exact Int.dvd_of_emod_eq_zero ( by rw [ Int.emod_eq_zero_of_dvd ] ; exact Int.modEq_iff_dvd.mp ha'.2.2.2.symm );
  · exact Int.dvd_of_emod_eq_zero ( by rw [ Int.emod_eq_zero_of_dvd ] ; exact Int.dvd_of_emod_eq_zero ( by rw [ Int.emod_eq_zero_of_dvd ] ; exact Int.modEq_iff_dvd.mp ha.2.2.2.symm ) )
/-- **Nonsquare fibers, `(1.15)`.** For admissible nonsquare `x`, the solutions are exactly
those obtained from a reduced seed `(r,s) ∈ S_x`, an exponent `n`, and independent signs. -/
theorem nonsquare_fiber {x y z : ℤ} (hx : Admissible x) (hns : ¬ IsSquare x) :
    IsSol x y z ↔
      ∃ r s, (r, s) ∈ Sx x ∧ ∃ n : ℕ,
        (y = Yseq x r s n ∨ y = -Yseq x r s n) ∧ (z = Zseq x r s n ∨ z = -Zseq x r s n) := by
  constructor;
  · intro h;
    obtain ⟨r, s, hr, hs, hrs⟩ : ∃ r s : ℤ, (r, s) ∈ Sx x ∧ ∃ n : ℕ, (pellIter x (ux x) (vx x) r s n).1 = |z| ∧ (pellIter x (ux x) (vx x) r s n).2 = |y| := by
      obtain ⟨r, s, hr, hs, hrs⟩ : ∃ r s : ℤ, (r, s) ∈ Rset x (Nx x) ∧ ∃ n : ℕ, (pellIter x (ux x) (vx x) r s n).1 = |z| ∧ (pellIter x (ux x) (vx x) r s n).2 = |y| := by
        obtain ⟨Z, Y, hZ, hY, hZY⟩ : ∃ Z Y : ℤ, 0 < Z ∧ 0 ≤ Y ∧ Z ^ 2 - x * Y ^ 2 = Nx x ∧ Z = |z| ∧ Y = |y| := by
          refine' ⟨ |z|, |y|, _, _, _, rfl, rfl ⟩ <;> norm_num [ hx.1, hx.2.1, hx.2.2.1, hx.2.2.2 ];
          · rintro rfl; have := hx.1; have := hx.2.1; have := hx.2.2.1; have := hx.2.2.2; simp_all +decide [ IsSol ] ;
            have : x ≤ 2 := Int.le_of_lt_add_one ( by nlinarith [ sq_nonneg ( x^2 ) ] ) ; interval_cases x <;> norm_num at *;
          · exact h;
        have := exists_seed_repr hx.1 hns ( show 0 < Nx x from ?_ ) hZ hY hZY.1;
        · grind;
        · unfold Nx;
          nlinarith [ sq_nonneg ( x^2 ), hx.1, show x > 1 from lt_of_le_of_ne ( by linarith [ hx.1 ] ) ( Ne.symm <| by rintro rfl; exact hns <| by norm_num ) ];
      exact ⟨ r, s, Sx_eq_Rset x ▸ hr, hs, hrs ⟩;
    exact ⟨ r, s, hr, hs, by cases abs_cases y <;> [ left; right ] <;> linarith! [ show Yseq x r s hs = ( pellIter x ( ux x ) ( vx x ) r s hs ).2 from rfl ], by cases abs_cases z <;> [ left; right ] <;> linarith! [ show Zseq x r s hs = ( pellIter x ( ux x ) ( vx x ) r s hs ).1 from rfl ] ⟩;
  · rintro ⟨ r, s, hrs, n, hy, hz ⟩;
    -- By definition of $Zseq$ and $Yseq$, we know that $(Zseq x r s n)^2 - x * (Yseq x r s n)^2 = Nx x$.
    have h_eq : (Zseq x r s n)^2 - x * (Yseq x r s n)^2 = Nx x := by
      apply (seed_gives_sol hx.1 hns hrs.1 hrs.2.1 hrs.2.2.1 n).right.right;
    unfold Nx at *; cases hy <;> cases hz <;> simp_all +decide [ IsSol ] ;
/--
**Theorem 1.1 (Complete classification).** Every integer solution of `(1.1)` is described
by exactly one of the three fiber families.
-/
theorem classification (x y z : ℤ) :
    IsSol x y z ↔
      (x = 1 ∧ (y = 1 ∨ y = -1) ∧ z = 0) ∨
      (∃ m, 3 ≤ m ∧ Odd m ∧ x = m ^ 2 ∧
        (∃ a ∈ Fm m, (y = Ym m a ∨ y = -Ym m a) ∧ (z = Zm m a ∨ z = -Zm m a))) ∨
      (Admissible x ∧ ¬ IsSquare x ∧ ∃ r s, (r, s) ∈ Sx x ∧ ∃ n : ℕ,
        (y = Yseq x r s n ∨ y = -Yseq x r s n) ∧ (z = Zseq x r s n ∨ z = -Zseq x r s n)) := by
  constructor;
  · intro h;
    by_cases hx : x = 1;
    · exact Or.inl <| by subst hx; exact ⟨ rfl, by have := fiber_x1.mp h; tauto ⟩ ;
    · by_cases hsq : IsSquare x;
      · obtain ⟨ m, rfl ⟩ := hsq;
        -- Since $m$ is odd and $m^2 \neq 1$, we have $m \geq 3$.
        have hm_ge_3 : 3 ≤ |m| := by
          have hm_ge_3 : Odd (m * m) := by
            have := ZXY2.sol_x_odd h; simp_all +decide [ parity_simps ] ;
          contrapose! hx; rcases abs_le.mp ( show |m| ≤ 2 by linarith ) with ⟨ hm₁, hm₂ ⟩ ; interval_cases m <;> trivial;
        refine Or.inr <| Or.inl ⟨ |m|, hm_ge_3, ?_, ?_, ?_ ⟩ <;> norm_num [ sq, abs_mul ] at *;
        · have := ZXY2.sol_x_odd h; simp_all +decide [ ← sq, parity_simps ] ;
          cases abs_cases m <;> simp +decide [ * ];
        · convert square_fiber ( show 3 ≤ |m| by linarith ) |>.1 _ using 1;
          grind +qlia;
      · exact Or.inr <| Or.inr <| ⟨ prop22 h, hsq, nonsquare_fiber ( prop22 h ) hsq |>.1 h ⟩;
  · rintro ( ⟨ rfl, rfl | rfl, rfl ⟩ | ⟨ m, hm₁, hm₂, rfl, a, ha₁, ha₂, ha₃ ⟩ | ⟨ hx₁, hx₂, r, s, hs₁, n, hn₁, hn₂ ⟩ ) <;> simp_all +decide [ ZXY2.IsSol ];
    · rcases ha₂ with ( rfl | rfl ) <;> rcases ha₃ with ( rfl | rfl ) <;> norm_num [ Ym, Zm ] at *;
      · have := ha₁.2.2.2; simp_all +decide [ Mm ] ;
        obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp this.symm;
        rw [ show ( ( m ^ 6 - 2 ) / a + a ) / 2 = k * m + a by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ; rw [ show ( ( m ^ 6 - 2 ) / a - a ) / ( 2 * m ) = k by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ;
        cases lt_or_gt_of_ne ( show a ≠ 0 from by rintro rfl; exact absurd ha₁.1 ( by norm_num ) ) <;> nlinarith [ Int.ediv_mul_cancel ( show a ∣ m ^ 6 - 2 from ha₁.2.1 ) ];
      · have := ha₁.2.2.2; simp_all +decide [ Mm ] ;
        obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp this.symm;
        rw [ show ( ( m ^ 6 - 2 ) / a + a ) / 2 = k * m + a by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ; rw [ show ( ( m ^ 6 - 2 ) / a - a ) / ( 2 * m ) = k by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ;
        cases lt_or_gt_of_ne ( show a ≠ 0 from by rintro rfl; exact absurd ha₁.1 ( by norm_num ) ) <;> nlinarith [ Int.ediv_mul_cancel ( show a ∣ m ^ 6 - 2 from ha₁.2.1 ) ];
      · have := ha₁.2.2.2; simp_all +decide [ Mm ] ;
        obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp this.symm;
        rw [ show ( ( m ^ 6 - 2 ) / a + a ) / 2 = k * m + a by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ; rw [ show ( ( m ^ 6 - 2 ) / a - a ) / ( 2 * m ) = k by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ;
        cases lt_or_gt_of_ne ( show a ≠ 0 from by rintro rfl; exact absurd ha₁.1 ( by norm_num ) ) <;> nlinarith [ Int.ediv_mul_cancel ( show a ∣ m ^ 6 - 2 from ha₁.2.1 ) ];
      · have := ha₁.2.2.2; simp_all +decide [ Mm ] ;
        obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp this.symm;
        rw [ show ( ( m ^ 6 - 2 ) / a + a ) / 2 = k * m + a by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ; rw [ show ( ( m ^ 6 - 2 ) / a - a ) / ( 2 * m ) = k by rw [ Int.ediv_eq_of_eq_mul_left ] <;> linarith ] ;
        cases lt_or_gt_of_ne ( show a ≠ 0 from by rintro rfl; exact absurd ha₁.1 ( by norm_num ) ) <;> nlinarith [ Int.ediv_mul_cancel ( show a ∣ m ^ 6 - 2 from ha₁.2.1 ) ];
    · have := nonsquare_fiber hx₁ hx₂ |>.2 ⟨ r, s, hs₁, n, hn₁, hn₂ ⟩ ; aesop;
/--
**Corollary 4.1.** The full equation has infinitely many integer solutions.
-/
theorem infinitely_many_solutions : {p : ℤ × ℤ × ℤ | IsSol p.1 p.2.1 p.2.2}.Infinite := by
  -- Apply `sol_none_or_infinite` to get the infiniteness of the set `S`.
  have h_inf : Set.Infinite {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1^2 - 3*p.2^2 = 25} := by
    apply ZXY2.sol_none_or_infinite ( show 0 < 3 by norm_num ) ( by rintro ⟨ r, hr ⟩ ; nlinarith [ show r ≤ 1 by nlinarith, show r ≥ -1 by nlinarith ] ) ( show 0 < 25 by norm_num ) |> Or.resolve_left <| by
                                                                                                                                                            exact Classical.not_not.2 ⟨ 5, 0, by norm_num ⟩;
  intro h_fin;
  refine h_inf <| Set.Finite.subset ( h_fin.image fun p : ℤ × ℤ × ℤ => ( p.2.2, p.2.1 ) ) ?_;
  intro p hp; use ( 3, p.2, p.1 ) ; simp_all +decide [ IsSol ] ;
/-! ## Section 5: Examples -/
/-- **Example 5.1.** Concrete members of the fiber `x = 3`. -/
theorem example_x3_solutions :
    IsSol 3 0 5 ∧ IsSol 3 5 10 ∧ IsSol 3 20 35 ∧ IsSol 3 75 130 ∧ IsSol 3 280 485 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> · unfold IsSol; norm_num
/-- **Example 5.2.** The solutions with `x = 9` include `(9, ±121, ±364)`. -/
theorem example_x9_solution : IsSol 9 121 364 := by unfold IsSol; norm_num
/-- **Example 5.3 (Admissibility is not sufficient).** The prime `43` is admissible, yet the
fiber `x = 43` is empty. -/
theorem example_x43_empty : ¬ ∃ y z : ℤ, IsSol 43 y z := by
  rintro ⟨ y, z, h ⟩;
  -- Write $y = 5y'$ and $z = 5z'$.
  obtain ⟨y', hy'⟩ : ∃ y', y = 5 * y' := by
    exact Int.dvd_of_emod_eq_zero ( by have := congr_arg ( · % 5 ) h; norm_num [ sq, Int.mul_emod, Int.sub_emod ] at this; have := Int.emod_nonneg y ( by decide : ( 5 : ℤ ) ≠ 0 ) ; have := Int.emod_nonneg z ( by decide : ( 5 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos y ( by decide : ( 5 : ℤ ) > 0 ) ; have := Int.emod_lt_of_pos z ( by decide : ( 5 : ℤ ) > 0 ) ; interval_cases y % 5 <;> interval_cases z % 5 <;> trivial )
  obtain ⟨z', hz'⟩ : ∃ z', z = 5 * z' := by
    exact Int.dvd_of_emod_eq_zero ( by have := congr_arg ( · % 5 ) h; norm_num [ sq, Int.add_emod, Int.sub_emod, Int.mul_emod, hy' ] at this; have := Int.emod_nonneg z ( by decide : ( 5 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos z ( by decide : ( 5 : ℤ ) > 0 ) ; interval_cases z % 5 <;> trivial );
  unfold IsSol at h; subst_vars; ring_nf at h; omega;
/-- `43` is admissible, witnessing that membership in `A` is not sufficient for solubility. -/
theorem example_43_admissible : Admissible 43 := by
  constructor <;> norm_num;
  norm_cast at *; intro p pp dp; have := Nat.le_of_dvd ( by decide ) dp; interval_cases p <;> trivial;
end ZXY2
