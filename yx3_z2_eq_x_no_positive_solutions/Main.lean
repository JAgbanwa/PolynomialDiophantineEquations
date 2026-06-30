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
set_option grind.warning false
/-!
# A Ljunggren–Nagell reduction
Formalisation of the paper "A Ljunggren–Nagell reduction", which proves that the
Diophantine equation `y(x³ − z²) = x` has no solution in positive integers, and more
precisely that the only solution with `x, y ≥ 1` and `z ≥ 0` is `(x, y, z) = (1, 1, 0)`.
The argument reduces the problem to the classical Ljunggren–Nagell input that the equation
`U² + 1 = A⁴B³` has no positive solution.  That input is the single external ingredient of
the paper, so here it is carried as an explicit hypothesis (`LjunggrenNagell`) rather than
re-proved.
-/
namespace LjunggrenNagellReduction
/-- **Theorem 1.1 (Ljunggren–Nagell input).**  The equation `U² + 1 = A⁴B³` has no solution
in integers `U, A, B` with `U ≥ 1` and `A, B ≥ 1`.  This is the only external ingredient of
the paper, and is carried as a hypothesis in the results below. -/
def LjunggrenNagell : Prop :=
  ∀ U A B : ℤ, 1 ≤ U → 1 ≤ A → 1 ≤ B → U ^ 2 + 1 ≠ A ^ 4 * B ^ 3
/-
**Lemma 2.1 (Coprime factors of a square).**  If `r, s` are positive coprime integers
whose product is a square, then both `r` and `s` are squares.
-/
lemma coprime_factors_of_sq {r s c : ℤ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hco : Int.gcd r s = 1) (h : r * s = c ^ 2) :
    (∃ a, r = a ^ 2) ∧ (∃ b, s = b ^ 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, r = a ^ 2 ∨ r = -a ^ 2 := by
    apply Int.sq_of_gcd_eq_one hco h
  obtain ⟨b, hb⟩ : ∃ b : ℤ, s = b ^ 2 ∨ s = -b ^ 2 := by
    have := Int.sq_of_gcd_eq_one ( show Int.gcd s r = 1 from Nat.Coprime.symm hco ) ( by linarith ) ; aesop;
  exact ⟨ ⟨ a, ha.resolve_right ( by nlinarith ) ⟩, ⟨ b, hb.resolve_right ( by nlinarith ) ⟩ ⟩
/-
**Lemma 2.2 (The quotient forced by the equation).**  For a solution with `x, y ≥ 1`,
`z ≥ 0`, we have `y ∣ x`; writing `d = x/y` we get `z² = d(d²y³ − 1)`, and if `z > 0` then
`d²y³ − 1 > 0`.
-/
lemma quotient_forced {x y z : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z)
    (heq : y * (x ^ 3 - z ^ 2) = x) :
    ∃ d : ℤ, 1 ≤ d ∧ x = d * y ∧ z ^ 2 = d * (d ^ 2 * y ^ 3 - 1) ∧
      (0 < z → 0 < d ^ 2 * y ^ 3 - 1) := by
  -- Set d = x/y; then d ≥ 1 (since x ≥ 1, y ≥ 1, d positive integer) and x = d*y.
  obtain ⟨d, hd⟩ : ∃ d, x = d * y := by
    exact exists_eq_mul_left_of_dvd ( dvd_of_mul_right_eq _ heq )
  have hd_pos : 1 ≤ d := by
    nlinarith
  subst hd
  use d
  simp_all +decide [ sq, mul_assoc ];
  exact ⟨ by nlinarith, fun hz' => by nlinarith [ pow_pos ( zero_lt_one.trans_le hy ) 3, pow_pos ( zero_lt_one.trans_le hd_pos ) 2 ] ⟩
/-
**Lemma 2.3 (The square quotient reduction).**  Every solution with `x, y ≥ 1`, `z ≥ 0`
either equals `(1, 1, 0)`, or yields integers `a, u ≥ 1` with `x = a²y`, `z = au` and
`u² + 1 = a⁴y³`.
-/
lemma square_quotient_reduction {x y z : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z)
    (heq : y * (x ^ 3 - z ^ 2) = x) :
    (x = 1 ∧ y = 1 ∧ z = 0) ∨
      ∃ a u : ℤ, 1 ≤ a ∧ 1 ≤ u ∧ x = a ^ 2 * y ∧ z = a * u ∧ u ^ 2 + 1 = a ^ 4 * y ^ 3 := by
  by_cases h_case : z = 0;
  · simp_all +decide [ mul_comm ];
    exact Or.inl ⟨ by nlinarith [ pow_pos ( zero_lt_one.trans_le hx ) 2, pow_pos ( zero_lt_one.trans_le hx ) 3, pow_pos ( zero_lt_one.trans_le hy ) 2, pow_pos ( zero_lt_one.trans_le hy ) 3 ], by nlinarith [ pow_pos ( zero_lt_one.trans_le hx ) 2, pow_pos ( zero_lt_one.trans_le hx ) 3, pow_pos ( zero_lt_one.trans_le hy ) 2, pow_pos ( zero_lt_one.trans_le hy ) 3 ] ⟩;
  · obtain ⟨ d, hd₁, hd₂, hd₃, hd₄ ⟩ := quotient_forced hx hy hz heq;
    -- By `coprime_factors_of_sq`, we get `d = a^2` and `d^2 y^3 - 1 = u^2` with `a, u ≥ 1`.
    obtain ⟨ a, ha₁, ha₂ ⟩ : ∃ a : ℤ, 1 ≤ a ∧ d = a ^ 2 := by
      have h_coprime : Int.gcd d (d ^ 2 * y ^ 3 - 1) = 1 := by
        norm_num [ show d ^ 2 * y ^ 3 - 1 = d * ( d * y ^ 3 ) - 1 by ring ];
      have := coprime_factors_of_sq hd₁ ( show 1 ≤ d ^ 2 * y ^ 3 - 1 from by nlinarith [ hd₄ ( lt_of_le_of_ne hz ( Ne.symm h_case ) ) ] ) h_coprime hd₃.symm;
      rcases this.1 with ⟨ a, rfl ⟩ ; exact ⟨ |a|, by cases abs_cases a <;> nlinarith, by simp +decide ⟩ ;
    obtain ⟨ u, hu₁, hu₂ ⟩ : ∃ u : ℤ, 1 ≤ u ∧ d ^ 2 * y ^ 3 - 1 = u ^ 2 := by
      use Int.natAbs ( z / a );
      simp_all +decide;
      exact ⟨ by rw [ abs_of_nonneg ( Int.ediv_nonneg hz ( by positivity ) ) ] ; exact Int.le_ediv_of_mul_le ( by positivity ) ( by nlinarith [ show z ≥ a by nlinarith [ show 0 < ( a ^ 2 ) ^ 2 * y ^ 3 - 1 from by nlinarith [ hd₄ ( lt_of_le_of_ne hz ( Ne.symm h_case ) ) ] ] ] ), by nlinarith [ Int.ediv_mul_cancel ( show a ∣ z from Int.pow_dvd_pow_iff two_ne_zero |>.1 <| hd₃.symm ▸ dvd_mul_right _ _ ) ] ⟩;
    refine Or.inr ⟨ a, u, ha₁, hu₁, ?_, ?_, ?_ ⟩ <;> subst_vars <;> ring_nf at *;
    · rw [ ← sq_eq_sq₀ ?_ ?_ ] <;> first | positivity | nlinarith;
    · linarith
/-
**Theorem 3.1.**  Assuming the Ljunggren–Nagell input, the only integer solution of
`y(x³ − z²) = x` with `x, y ≥ 1` and `z ≥ 0` is `(x, y, z) = (1, 1, 0)`.
-/
theorem only_solution (hLN : LjunggrenNagell) {x y z : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 0 ≤ z) (heq : y * (x ^ 3 - z ^ 2) = x) :
    x = 1 ∧ y = 1 ∧ z = 0 := by
  obtain h | ⟨ a, u, ha, hu, rfl, rfl, h ⟩ := square_quotient_reduction hx hy hz heq <;> simp_all +decide;
  exact absurd ( hLN u a y hu ha hy ) ( by norm_num [ h ] )
/-
**Corollary 3.2.**  Assuming the Ljunggren–Nagell input, the equation `y(x³ − z²) = x`
has no solution in positive integers `x, y, z`.
-/
theorem no_positive_solution (hLN : LjunggrenNagell) {x y z : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    y * (x ^ 3 - z ^ 2) ≠ x := by
  have := LjunggrenNagellReduction.only_solution hLN hx hy ( by linarith );
  grind +splitImp
/-!
## Appendix A. Gaussian-integer form of the quoted input
Here `GaussianInt = ℤ√(-1) = ℤ[i]`, with `Zsqrtd.norm ⟨r, s⟩ = r² + s²`.  We write `U + i` as
the Gaussian integer `⟨U, 1⟩`.
-/
/-- The Gaussian integer `U + i`. -/
def gaussAdd (U : ℤ) : GaussianInt := ⟨U, 1⟩
@[simp] lemma gaussAdd_norm (U : ℤ) : (gaussAdd U).norm = U ^ 2 + 1 := by
  simp [gaussAdd, Zsqrtd.norm_def]; ring
/-
**Proposition A.1 (parity).**  If `U² + 1 = A⁴B³` with `U, A, B ≥ 1`, then `U` is even
and `A` and `B` are odd.
-/
lemma prop_A1_parity {U A B : ℤ} (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : U ^ 2 + 1 = A ^ 4 * B ^ 3) :
    Even U ∧ Odd A ∧ Odd B := by
  apply_fun fun n => n % 4 at h; rcases Int.even_or_odd' U with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' A with ⟨ l, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ m, rfl | rfl ⟩ <;> ring_nf at h <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
  have := Int.emod_nonneg m four_pos.ne'; have := Int.emod_lt_of_pos m four_pos; interval_cases m % 4 <;> contradiction;
/-
**Proposition A.1 (norm converse).**  Taking norms in an identity `U + i = ε·α⁴·β³` with
`ε` a unit recovers an equation of the shape `U² + 1 = N(α)⁴·N(β)³`.  This is the easy half of
the equivalence asserted in Proposition A.1.
-/
lemma prop_A1_norm_converse (U : ℤ) (α β ε : GaussianInt) (hε : IsUnit ε)
    (hfact : gaussAdd U = ε * α ^ 4 * β ^ 3) :
    U ^ 2 + 1 = α.norm ^ 4 * β.norm ^ 3 := by
  have := congr_arg Zsqrtd.norm hfact; norm_num [ pow_succ, mul_assoc ] at this;
  rw [ show Zsqrtd.norm ε = 1 by
        rw [ isUnit_iff_exists_inv ] at hε;
        obtain ⟨ b, hb ⟩ := hε; have := congr_arg Zsqrtd.norm hb; norm_num at this;
        cases' Int.eq_one_or_neg_one_of_mul_eq_one this with h h <;> simp_all +decide [ Zsqrtd.norm ];
        nlinarith ] at this; linear_combination' this;
/-
**Proposition A.1 (coprimality of the factors).**  When `U` is even (equivalently, `U²+1`
is odd), the Gaussian integers `U + i` and `U - i` are coprime in `ℤ[i]`.  This is the key
Gaussian observation underlying the factorisation in Proposition A.1.
-/
lemma prop_A1_coprime {U : ℤ} (hU : Even U) :
    IsCoprime (gaussAdd U) (star (gaussAdd U)) := by
  obtain ⟨ k, hk ⟩ := hU;
  obtain ⟨ a, b, h ⟩ : ∃ a b : ℤ, 2 * a + (U ^ 2 + 1) * b = 1 := by
    exact ⟨ - ( U ^ 2 / 2 ), 1, by linarith [ Int.ediv_mul_cancel ( show 2 ∣ U ^ 2 from even_iff_two_dvd.mp ( by simp +decide [ hk, parity_simps ] ) ) ] ⟩;
  use ⟨ b, 0 ⟩ * star ( gaussAdd U ) + ⟨ 0, -a ⟩, ⟨ 0, a ⟩ ; ext <;> norm_num [ gaussAdd ] <;> ring_nf at h ⊢ ; simp_all +decide [ ← two_mul ] ;
/-- Associated Gaussian integers have equal norm. -/
lemma gauss_norm_associated {x y : GaussianInt} (h : Associated x y) :
    x.norm = y.norm := by
  obtain ⟨u, rfl⟩ := h.symm
  rw [Zsqrtd.norm_mul]
  have hu : ((u : GaussianInt)).norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  have hnn : 0 ≤ ((u : GaussianInt)).norm := GaussianInt.norm_nonneg _
  have : ((u : GaussianInt)).norm = 1 := by omega
  rw [this, mul_one]
/-
**Extraction lemma.**  Let `w` be a nonzero Gaussian integer coprime to its conjugate
`star w`.  If `(M : ℤ[i])^k` divides `w · star w` (with `M ≥ 1` a rational integer and `k ≠ 0`),
then the `M`-part splits off as a perfect `k`-th power dividing `w`: there is `d` with `dᵏ ∣ w`
and `N(d) = M`.
This is the engine behind the Gaussian factorisation of Proposition A.1: it isolates the
fourth-power (resp. cube) part contributed by `A` (resp. `B`).
-/
lemma gauss_extract {w : GaussianInt} (hco : IsCoprime w (star w))
    {M : ℤ} (hM : 1 ≤ M) {k : ℕ} (hk : k ≠ 0)
    (hdvd : ((M : GaussianInt)) ^ k ∣ w * star w) :
    ∃ d : GaussianInt, d ^ k ∣ w ∧ d.norm = M := by
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : GaussianInt, a ∣ w ∧ b ∣ star w ∧ (M : GaussianInt) ^ k = a * b := by
    have := @exists_dvd_and_dvd_of_dvd_mul;
    exact this hdvd;
  -- From `hco : IsCoprime w (star w)`, `a ∣ w`, `b ∣ star w`, deduce `hab : IsCoprime a b` using `hco.of_dvd_left` / `IsCoprime.of_isCoprime_of_dvd_left` and the `_right` variant.
  have hab_coprime : IsCoprime a b := by
    exact hco.of_isCoprime_of_dvd_left ha |> IsCoprime.of_isCoprime_of_dvd_right <| hb;
  -- Apply `exists_associated_pow_of_mul_eq_pow' hab_coprime (k := k)` to `a * b = (M:ℤ[i])^k` (the hypothesis from step 1, symmetrized) to get `d` with `Associated (d ^ k) a`.
  obtain ⟨d, hd⟩ : ∃ d : GaussianInt, Associated (d ^ k) a := by
    convert exists_associated_pow_of_mul_eq_pow' hab_coprime _;
    exacts [ ↑M, hab.symm ];
  -- And `star b ∣ a * b` (= `star a * star b`); since `IsCoprime (star b) b`, `star b ∣ a` (use `IsCoprime.dvd_of_dvd_mul_right`).
  have h_star_b_div_a : star b ∣ a := by
    have h_star_b_div_a : star b ∣ a * b := by
      have h_star_b_div_a : star b ∣ star (a * b) := by
        simp +decide;
      convert h_star_b_div_a using 1 ; simp +decide [ ← hab ];
    refine' IsCoprime.dvd_of_dvd_mul_right _ h_star_b_div_a;
    have h_star_b_coprime_b : IsCoprime (star b) (star w) := by
      obtain ⟨ c, hc ⟩ := hb;
      simp_all +decide [ isCoprime_comm ];
      obtain ⟨ u, v, h ⟩ := hco;
      replace h := congr_arg Star.star h ; simp_all +decide [ mul_comm ];
      exact ⟨ star u, star v * star c, by linear_combination' h ⟩;
    exact h_star_b_coprime_b.of_isCoprime_of_dvd_right hb;
  -- Therefore `Associated a (star b)` (from mutual divisibility, `associated_of_dvd_dvd`). So `N a = N (star b) = N b` using `gauss_norm_associated` and `Zsqrtd.norm_conj`.
  have h_norm_eq : a.norm = b.norm := by
    have h_assoc : Associated a (star b) := by
      have h_a_div_star_b : a ∣ star b := by
        have h_a_div_star_b : a ∣ star a * star b := by
          have h_a_div_star_b : a ∣ star (a * b) := by
            simp +decide [ ← hab ];
            exact hab.symm ▸ dvd_mul_right _ _;
          convert h_a_div_star_b using 1 ; simp +decide;
        refine' IsCoprime.dvd_of_dvd_mul_left _ h_a_div_star_b;
        obtain ⟨ u, hu ⟩ := ha;
        obtain ⟨ v, hv ⟩ := hco;
        obtain ⟨ b, hb ⟩ := hv;
        exact ⟨ v * u, b * star u, by rw [ hu ] at hb; simpa [ mul_assoc, mul_comm, mul_left_comm ] using hb ⟩;
      exact associated_of_dvd_dvd h_a_div_star_b h_star_b_div_a;
    have := gauss_norm_associated h_assoc; aesop;
  -- Now `N a * N b = N (a*b) = N ((M:ℤ[i])^k)` (`Zsqrtd.norm_mul`, `Zsqrtd.norm_pow`). And `N (M:ℤ[i]) = M^2` (compute via `Zsqrtd.norm_def` or `Zsqrtd.norm_intCast`; `GaussianInt = Zsqrtd (-1)`, so `N ⟨M,0⟩ = M^2 - (-1)*0 = M^2`). So `N (M:ℤ[i])^k = (M^2)^k = M^(2k)`. Combined with `N a = N b`, get `(N a)^2 = (M^k)^2`. Since `0 ≤ N a` (`GaussianInt.norm_nonneg`) and `0 ≤ M^k` (from `1 ≤ M`), conclude `N a = M^k` (e.g. `nlinarith`/`pow_left_injective`/`abs_eq_abs`).
  have h_norm_a : a.norm = M ^ k := by
    replace hab := congr_arg Zsqrtd.norm hab ; simp_all +decide [ Zsqrtd.norm_mul ];
    simp_all +decide [ Zsqrtd.norm ];
    norm_cast at *;
    erw [ Zsqrtd.re_intCast, Zsqrtd.im_intCast ] at hab ; nlinarith [ pow_pos ( zero_lt_one.trans_le hM ) k ];
  -- From `Associated (d^k) a`, `gauss_norm_associated` and `Zsqrtd.norm_pow` give `(N d)^k = N a = M^k`. With `0 ≤ N d` (`GaussianInt.norm_nonneg`), `0 ≤ M`, and `k ≠ 0`, deduce `N d = M` (`pow_left_injective` on nonnegatives, or `pow_left_strictMono`/`nlinarith` per small `k`).
  have h_norm_d : d.norm ^ k = M ^ k := by
    have h_norm_d : d.norm ^ k = a.norm := by
      have := gauss_norm_associated hd;
      convert this using 1;
      exact Nat.recOn k ( by norm_num ) fun n ihn => by simp +decide [ *, pow_succ' ] ;
    rw [h_norm_d, h_norm_a];
  refine' ⟨ d, _, _ ⟩;
  · exact dvd_trans ( hd.dvd ) ha;
  · exact ( pow_left_inj₀ ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ Zsqrtd.norm ] ; norm_num; nlinarith ) ) ) ) ) ) ( by positivity ) hk ) |>.1 h_norm_d
/-
**Proposition A.1 (Gaussian factorisation -- full existence).**  If `U² + 1 = A⁴B³` with
`U, A, B ≥ 1`, then there are Gaussian integers `α, β` and a unit `ε` with `U + i = ε·α⁴·β³`,
`N(α) = A` and `N(β) = B`.
-/
theorem prop_A1 {U A B : ℤ} (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : U ^ 2 + 1 = A ^ 4 * B ^ 3) :
    ∃ (α β ε : GaussianInt), IsUnit ε ∧
      gaussAdd U = ε * α ^ 4 * β ^ 3 ∧ α.norm = A ∧ β.norm = B := by
  obtain ⟨d, hd1, hd2⟩ : ∃ d : GaussianInt, d ^ 4 ∣ gaussAdd U ∧ d.norm = A := by
    apply gauss_extract;
    · have := prop_A1_parity hU hA hB h; exact prop_A1_coprime this.1;
    · grind;
    · norm_num;
    · -- By definition of `gaussAdd`, we know that `gaussAdd U * star (gaussAdd U) = U^2 + 1`.
      have h_gauss_mul : gaussAdd U * star (gaussAdd U) = (U^2 + 1 : GaussianInt) := by
        have hmc := (Zsqrtd.norm_eq_mul_conj (gaussAdd U)).symm
        rw [gaussAdd_norm] at hmc
        rw [hmc]; push_cast; ring
      exact h_gauss_mul.symm ▸ mod_cast h.symm ▸ ⟨ B ^ 3, by ring ⟩;
  obtain ⟨w1, hw1⟩ : ∃ w1 : GaussianInt, gaussAdd U = d ^ 4 * w1 := hd1
  have hNw1 : w1.norm = B ^ 3 := by
    apply_fun Zsqrtd.norm at hw1;
    simp_all +decide [ Zsqrtd.norm_mul, pow_succ ];
    exact hw1.resolve_right ( by positivity ) ▸ rfl;
  -- Step D (extract the cube). Apply `gauss_extract hco1 (M := B) (hM := hB) (k := 3) (hk := by norm_num)` with `hdvd : (B:GaussianInt)^3 ∣ w1 * star w1` (it equals it, so `dvd_refl`/`Dvd.intro`). Get `e` with `he1 : e^3 ∣ w1` and `he2 : N e = B`.
  obtain ⟨e, he1, he2⟩ : ∃ e : GaussianInt, e ^ 3 ∣ w1 ∧ e.norm = B := by
    apply gauss_extract;
    · have hco1 : IsCoprime (gaussAdd U) (star (gaussAdd U)) := by
        apply prop_A1_coprime;
        apply (prop_A1_parity hU hA hB h).left;
      obtain ⟨ a, b, h ⟩ := hco1;
      use a * d ^ 4, b * star d ^ 4;
      convert h using 1 ; rw [ hw1 ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    · linarith;
    · norm_num;
    · rw [ ← Zsqrtd.norm_eq_mul_conj ] ; norm_cast ; aesop;
  obtain ⟨c, hc⟩ : ∃ c : GaussianInt, w1 = e ^ 3 * c := he1
  have hc_unit : IsUnit c := by
    simp_all +decide [ Zsqrtd.norm_mul, pow_succ ];
    simp_all +decide [ Zsqrtd.norm ];
    simp_all +decide [ ne_of_gt ( zero_lt_one.trans_le hB ) ];
    rw [ isUnit_iff_exists_inv ];
    exact ⟨ ⟨ c.re, -c.im ⟩, by ext <;> simp +decide <;> linarith ⟩;
  exact ⟨ d, e, c, hc_unit, by rw [ hw1, hc ] ; ring, hd2, he2 ⟩
end LjunggrenNagellReduction
