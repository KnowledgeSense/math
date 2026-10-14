import BoseBurton.BoseZCoefficients

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

/-- The literal restricted-Z coefficient row on each vector subspace. -/
def restrictedZRow (W U : Submodule K V) : Polynomial ℤ :=
  ∑ i ∈ range (finrank K U+1), monomial i
    ((projectiveRankEnumerator K U).coeff i -
      (projectiveRankEnumerator K (W.comap U.subtype)).coeff (max i (finrank K U-i)))

omit [Module.Finite K V] in
theorem restrictedZRow_coeff (W U : Submodule K V) (i : ℕ) :
    (restrictedZRow W U).coeff i = if i ≤ finrank K U then
      (projectiveRankEnumerator K U).coeff i -
        (projectiveRankEnumerator K (W.comap U.subtype)).coeff (max i (finrank K U-i)) else 0 := by
  by_cases h : i ≤ finrank K U <;> simp [restrictedZRow, coeff_monomial, h]

theorem restricted_spanZ_eq_row (W U : Submodule K V) (hU : ¬ U ≤ W) :
    spanZ (W.comap U.subtype) (restricted_deleted_subspace_proper W U hU) = restrictedZRow W U := by
  ext i
  rw [restrictedZRow_coeff]
  by_cases hi : i ≤ finrank K U
  · rw [ite_eq_left hi]
    exact spanZ_coeff _ _ i hi
  · rw [ite_eq_right hi]
    exact spanZ_coeff_above _ _ i (by omega)

omit [Module.Finite K V] in
theorem lower_zKernel_restriction (W U : Submodule K V) (hU : ¬ U ≤ W) :
    zKernel (spanRank W) ⊥ ⟨U, Or.inr hU⟩ =
      spanZ (W.comap U.subtype) (restricted_deleted_subspace_proper W U hU) := by
  have h := zKernel_interval_transport (restrictionFlatEmbedding W U)
    (restrictionFlatEmbedding_fills W U)
    (spanRank (W.comap U.subtype)) (spanRank W)
    (fun a b => by
      change finrank K (restrictionFlatEmbedding W U b).1 -
        finrank K (restrictionFlatEmbedding W U a).1 = _
      rw [restrictionFlatEmbedding_rank, restrictionFlatEmbedding_rank]
      rfl)
    ⊥ (spanTop (W.comap U.subtype) (restricted_deleted_subspace_proper W U hU))
  rw [restrictionFlatEmbedding_bot, restrictionFlatEmbedding_top W U hU] at h
  exact h

theorem lower_zKernel_eq_restrictedRow (W U : Submodule K V) (hU : ¬ U ≤ W) :
    zKernel (spanRank W) ⊥ ⟨U, Or.inr hU⟩ = restrictedZRow W U := by
  rw [lower_zKernel_restriction W U hU, restricted_spanZ_eq_row W U hU]

end BoseBurton
