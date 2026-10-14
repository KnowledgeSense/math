import BoseBurton.ActualFlatSum
import BoseBurton.FlatRankSums
import BoseBurton.RankZRows
import BoseBurton.ProjectiveYEvaluation

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V] [Finite V]

theorem projectiveY_quotient_real (U : Submodule K V) :
    (projectiveY K (V ⧸ U)).map (Int.castRingHom ℝ) =
      projectiveRow (Fintype.card K : ℝ) (finrank K V-finrank K U) := by
  rw [projectiveY_eq_projectiveRow]
  have h := Submodule.finrank_quotient_add_finrank U
  congr 1
  omega

/-- The genuine inverse-Z polynomial, grouped by actual flat rank. -/
theorem spanY_rank_sum (W : Submodule K V) (hW : W ≠ ⊤) :
    (spanY W hW).map (Int.castRingHom ℝ) =
      -(∑ d ∈ Icc 1 (finrank K V), C ((-1 : ℝ)^d) *
        restrictedRankRow (Fintype.card K : ℝ) (finrank K V) (finrank K W) d *
        projectiveRow (Fintype.card K : ℝ) (finrank K V-d)) := by
  rw [spanY_actual_flat_sum, Polynomial.map_neg, Polynomial.map_sum]
  have hs : (∑ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W),
      (C ((-1 : ℤ)^(finrank K U)) * restrictedZRow W U * projectiveY K (V ⧸ U)).map (Int.castRingHom ℝ)) =
      ∑ U ∈ univ.filter (fun U : Submodule K V => ¬ U ≤ W),
        C ((-1 : ℝ)^(finrank K U)) * (restrictedZRow W U).map (Int.castRingHom ℝ) *
          projectiveRow (Fintype.card K : ℝ) (finrank K V-finrank K U) := by
    apply sum_congr rfl
    intro U _
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, projectiveY_quotient_real]
    congr 2
    simp
  rw [hs, nondeleted_sum_by_rank]
  congr 1
  apply sum_congr rfl
  intro d _
  calc
    _ = ∑ U : NondeletedRankSubspace W d, C ((-1 : ℝ)^d) *
        (restrictedZRow W U.1).map (Int.castRingHom ℝ) *
          projectiveRow (Fintype.card K : ℝ) (finrank K V-d) := by
      apply sum_congr rfl
      intro U _
      rw [U.2.1]
    _ = C ((-1 : ℝ)^d) *
        (∑ U : NondeletedRankSubspace W d, (restrictedZRow W U.1).map (Int.castRingHom ℝ)) *
          projectiveRow (Fintype.card K : ℝ) (finrank K V-d) := by
      rw [mul_sum, sum_mul]
    _ = _ := by rw [summed_restrictedZ_polynomial]

end BoseBurton
