import RequestProject
import Challenge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Solutions to the challenge statements

Every statement of `Challenge.lean` is discharged here from the development in
`RequestProject.lean`.
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
