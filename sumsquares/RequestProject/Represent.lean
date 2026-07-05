import RequestProject.SumTwoSquares
import RequestProject.PellAux
/-!
# The tangent construction for `R(t) = t³ + f`, `Q(x) = x²`
This file assembles the core of Algorithm 2.2 for the special families used in
Section 3 of the paper: `R(t) = t³ + f`, `Q(x) = x²`, so that `P(x) = x⁶ + f`.
* `cube_repr` is the tangent identity (7) combined with the division property (*).
* `cube_sqSum_infinite` gives infinitely many `x` with `x⁶ + f ∈ S₂`.
* `cube_sqSum_even_infinite` gives infinitely many *even* `x` with `x⁶ + f ∈ S₂`.
* `sqSum_even_split` / `sqSum_odd_split` select a representation of the required
  parity, used to produce the actual `(y, z)` solving the target equations.
* `infinite_of_first_proj` packages "infinitely many `x`" into "the solution set is
  infinite".
-/
namespace SumSquares
open scoped BigOperators
/-
Equation (12)/(7): if `v² = 4(u³+f)x² − u(u³−8f)` and `x⁶+f > 0`, and `4(u³+f)`
is itself a sum of two squares, then `x⁶+f` is a sum of two squares.
-/
lemma cube_repr {f u x v : ℤ} (hM : 0 < u ^ 3 + f)
    (hMs : SqSum (4 * (u ^ 3 + f))) (hpos : 0 < x ^ 6 + f)
    (h : v ^ 2 = 4 * (u ^ 3 + f) * x ^ 2 - u * (u ^ 3 - 8 * f)) :
    SqSum (x ^ 6 + f) := by
  -- Set M := u^3+f.
  set M : ℤ := u^3 + f;
  -- Then $4M(x^6 + f) = (2M + 3u^2(x^2 - u))^2 + ((x^2 - u)v)^2$.
  have hkey : 4 * M * (x^6 + f) = (2 * M + 3 * u^2 * (x^2 - u))^2 + ((x^2 - u) * v)^2 := by
    grobner;
  convert sqSum_div ( show 0 < 4 * M by positivity ) ( show 0 < x ^ 6 + f by positivity ) hMs ⟨ _, _, hkey ⟩ using 1
/-
The set of integers `x` with `x⁶ + f` a sum of two squares is infinite.
-/
lemma cube_sqSum_infinite {f u : ℤ} (hM : 0 < u ^ 3 + f)
    (hMs : SqSum (4 * (u ^ 3 + f)))
    (hns : ¬ IsSquare (4 * (u ^ 3 + f)))
    {x0 v0 : ℤ} (hx0 : 0 < x0) (hv0 : 0 < v0)
    (hseed : v0 ^ 2 = 4 * (u ^ 3 + f) * x0 ^ 2 - u * (u ^ 3 - 8 * f)) :
    {x : ℤ | 0 < x ∧ SqSum (x ^ 6 + f)}.Infinite := by
  -- By `aux_infinite`, we get infinitely many `x` with `0 < x` and `∃ v, v^2 = a*x^2 + c`.
  have hA : Set.Infinite {x : ℤ | 0 < x ∧ ∃ v : ℤ, v^2 = 4 * (u^3 + f) * x^2 - u * (u^3 - 8 * f)} := by
    convert SumSquares.aux_infinite ( show 0 < 4 * ( u ^ 3 + f ) by linarith ) hns hx0 hv0 hseed using 1;
  -- Let `Bad := {x : ℤ | ¬ (0 < x^6+f)}`. Show `Bad` is finite: if `x ∈ Bad` then `x^6+f ≤ 0`, so `x^6 ≤ -f`; since `|x|≥1` implies `x^6 ≥ x^2 ≥ |x|`, we get `|x| ≤ |f|`, hence `Bad ⊆ Set.Icc (-(|f|)) (|f|)` which is finite (`Set.finite_Icc`).
  have hBadFinite : Set.Finite {x : ℤ | ¬(0 < x^6 + f)} := by
    exact Set.Finite.subset ( Set.finite_Icc ( - ( |f| + 1 ) ) ( |f| + 1 ) ) fun x hx => ⟨ by cases abs_cases f <;> nlinarith [ sq_nonneg ( x^2 - 1 ), hx.out ], by cases abs_cases f <;> nlinarith [ sq_nonneg ( x^2 - 1 ), hx.out ] ⟩;
  exact hA.diff hBadFinite |> Set.Infinite.mono fun x hx => ⟨ hx.1.1, by simpa using cube_repr hM hMs ( by aesop ) hx.1.2.choose_spec ⟩
/-
The set of *even* integers `x` with `x⁶ + f` a sum of two squares is infinite.
Here the auxiliary equation is taken in the variable `w` with `x = 2w`, so its
leading coefficient is `16(u³+f)`.
-/
lemma cube_sqSum_even_infinite {f u : ℤ} (hM : 0 < u ^ 3 + f)
    (hMs : SqSum (4 * (u ^ 3 + f)))
    (hns : ¬ IsSquare (16 * (u ^ 3 + f)))
    {w0 v0 : ℤ} (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hseed : v0 ^ 2 = 16 * (u ^ 3 + f) * w0 ^ 2 - u * (u ^ 3 - 8 * f)) :
    {x : ℤ | 0 < x ∧ Even x ∧ SqSum (x ^ 6 + f)}.Infinite := by
  -- Let $a = 16(u^3 + f)$ and $c = -u(u^3 - 8f)$.
  set a := 16 * (u ^ 3 + f)
  set c := -u * (u ^ 3 - 8 * f);
  -- By `aux_infinite`, there are infinitely many $w > 0$ such that $v^2 = a*w^2 + c$.
  have hW : {w : ℤ | 0 < w ∧ ∃ v : ℤ, v^2 = a * w^2 + c}.Infinite := by
    convert aux_infinite ( show 0 < a by positivity ) hns hw0 hv0 _ using 1;
    linear_combination' hseed;
  -- Let $Bad := {w : ℤ | ¬ (0 < (2 * w) ^ 6 + f)}$, which is finite by the same bound argument as in `cube_sqSum_infinite`.
  have hBadFinite : {w : ℤ | ¬ (0 < (2 * w) ^ 6 + f)}.Finite := by
    refine Set.Finite.subset ( Set.finite_Icc ( - ( |f| + 1 ) ) ( |f| + 1 ) ) ?_;
    intro w hw; constructor <;> cases abs_cases f <;> nlinarith [ sq_nonneg ( w ^ 2 - 1 ), hw.out ] ;
  -- Consider the image of $W \setminus Bad$ under the map $w \mapsto 2w$.
  have h_image : Set.Infinite (Set.image (fun w => 2 * w) ({w : ℤ | 0 < w ∧ ∃ v : ℤ, v^2 = a * w^2 + c} \ {w : ℤ | ¬ (0 < (2 * w) ^ 6 + f)})) := by
    refine Set.Infinite.image ?_ <| hW.diff hBadFinite;
    exact fun x hx y hy hxy => mul_left_cancel₀ two_ne_zero hxy;
  refine h_image.mono ?_;
  simp +contextual [ Set.image_subset_iff ];
  intro w hw; obtain ⟨ hw₁, v, hv ⟩ := hw.1; exact ⟨ by linarith, by
    convert cube_repr hM hMs ( show 0 < ( 2 * w ) ^ 6 + f from not_le.mp hw.2 ) _ using 1;
    exacts [ v, by linear_combination' hv ] ⟩ ;
/-
Parity selection for `f ≡ 0 (mod 4)`: choose a representation `x⁶+f = A²+B²`
with `B` even and `A ≡ x (mod 2)`.
-/
lemma sqSum_even_split {f x : ℤ} (hf : f % 4 = 0) (h : SqSum (x ^ 6 + f)) :
    ∃ A B : ℤ, x ^ 6 + f = A ^ 2 + B ^ 2 ∧ A % 2 = x % 2 ∧ B % 2 = 0 := by
  cases' h with A hA;
  obtain ⟨ B, hB ⟩ := hA;
  by_cases hx : x % 2 = 0;
  · have h_even : A % 2 = 0 ∧ B % 2 = 0 := by
      replace hB := congr_arg ( · % 4 ) hB ; rcases Int.even_or_odd' A with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ l, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod, hx, hf ] at hB ⊢;
      · rw [ ← Int.emod_add_mul_ediv x 2, hx ] at hB; ring_nf at hB; norm_num [ Int.add_emod, Int.mul_emod ] at hB;
      · rw [ ← Int.emod_add_mul_ediv x 2, hx ] at hB; ring_nf at hB; norm_num [ Int.add_emod, Int.mul_emod ] at hB;
      · rw [ ← Int.emod_add_mul_ediv x 2, hx ] at hB; ring_nf at hB; norm_num [ Int.add_emod, Int.mul_emod ] at hB;
    grind;
  · rcases Int.even_or_odd' A with ⟨ a, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ b, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
    · obtain ⟨ k, rfl ⟩ := hf; replace hB := congr_arg ( · % 4 ) hB ; rcases Int.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
    · exact ⟨ 2 * b + 1, 2 * a, by linarith, by norm_num [ Int.add_emod, Int.mul_emod, hx ], by norm_num [ Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod ] ⟩;
    · exact ⟨ a * 2 + 1, b * 2, by linarith, by norm_num [ Int.add_emod, Int.mul_emod, hx ], by norm_num [ Int.dvd_iff_emod_eq_zero ] ⟩;
    · obtain ⟨ k, rfl ⟩ := hf; replace hB := congr_arg ( · % 4 ) hB ; rcases Int.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod ] at *;
/-
Parity selection for `f ≡ 1 (mod 4)`: choose a representation `x⁶+f = A²+B²`
with `B` odd and `A ≡ x (mod 2)`.
-/
lemma sqSum_odd_split {f x : ℤ} (hf : f % 4 = 1) (h : SqSum (x ^ 6 + f)) :
    ∃ A B : ℤ, x ^ 6 + f = A ^ 2 + B ^ 2 ∧ A % 2 = x % 2 ∧ B % 2 = 1 := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : ℤ, x^6 + f = A^2 + B^2 := by
    exact h;
  by_cases hx_even : Even x;
  · rcases hx_even with ⟨ k, rfl ⟩;
    rcases Int.even_or_odd' A with ⟨ a, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ b, rfl | rfl ⟩; all_goals grind;
  · rcases Int.even_or_odd' A with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' B with ⟨ l, rfl | rfl ⟩ <;> simp_all +decide [ parity_simps ];
    · replace hAB := congr_arg ( · % 4 ) hAB ; rcases hx_even with ⟨ m, rfl ⟩ ; ring_nf at hAB ; norm_num [ Int.add_emod, Int.mul_emod, hf ] at hAB;
    · replace hAB := congr_arg ( · % 4 ) hAB ; rcases hx_even with ⟨ m, rfl ⟩ ; ring_nf at hAB ; norm_num [ Int.add_emod, Int.mul_emod, hf ] at hAB;
    · obtain ⟨ m, rfl ⟩ := hx_even; replace hAB := congr_arg ( · % 4 ) hAB ; rcases Int.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' l with ⟨ l, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.mul_emod, hf ] at hAB;
    · grind +revert
/-
Packaging via an explicit injective family.
-/
lemma infinite_of_inj {P : ℤ → ℤ → ℤ → Prop} (g : ℕ → ℤ × ℤ × ℤ)
    (hinj : Function.Injective g)
    (hmem : ∀ n, P (g n).1 (g n).2.1 (g n).2.2) :
    {p : ℤ × ℤ × ℤ | P p.1 p.2.1 p.2.2}.Infinite := by
  exact Set.infinite_of_injective_forall_mem hinj hmem
/-
Packaging: if infinitely many `x` admit a solution `(y, z)` of a relation `P`,
then the full solution set `{(x,y,z) | P x y z}` is infinite.
-/
lemma infinite_of_first_proj {P : ℤ → ℤ → ℤ → Prop} {S : Set ℤ} (hS : S.Infinite)
    (hsol : ∀ x ∈ S, ∃ y z : ℤ, P x y z) :
    {p : ℤ × ℤ × ℤ | P p.1 p.2.1 p.2.2}.Infinite := by
  intro H; exact hS <| Set.Finite.subset ( H.image fun p : ℤ × ℤ × ℤ ↦ p.1 ) fun a h ↦ by obtain ⟨ y, z, hyz ⟩ := hsol a h; aesop;
/-
Packaging with a reparametrization `φ` of the first coordinate.
-/
lemma infinite_of_first_proj_comp {P : ℤ → ℤ → ℤ → Prop} {S : Set ℤ} (hS : S.Infinite)
    (φ : ℤ → ℤ) (hφ : Set.InjOn φ S)
    (hsol : ∀ w ∈ S, ∃ y z : ℤ, P (φ w) y z) :
    {p : ℤ × ℤ × ℤ | P p.1 p.2.1 p.2.2}.Infinite := by
  intro H;
  exact hS ( Set.Finite.of_finite_image ( Set.Finite.subset ( H.image fun p : ℤ × ℤ × ℤ => p.1 ) fun x hx => by aesop ) hφ )
end SumSquares
