import BoseBurton.FlatSums
import BoseBurton.IntervalInvariants
import BoseBurton.ProjectiveDuality
import BoseBurton.ZIncidenceTransport
import BoseBurton.ProjectiveEvaluation

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

def spanZ (W : Submodule K V) (hW : W ≠ ⊤) : Polynomial ℤ :=
  zKernel (spanRank W) ⊥ (spanTop W hW)

omit [Module.Finite K V] in
theorem span_interval_univ (W : Submodule K V) (hW : W ≠ ⊤) :
    Icc (⊥ : FlatSpan W) (spanTop W hW) = univ := by
  ext U
  simp only [mem_Icc, bot_le, true_and, mem_univ, iff_true]
  exact show U.1 ≤ (⊤ : Submodule K V) from le_top

omit [Module.Finite K V] in
theorem subspace_contained_rank_sum (W : Submodule K V) :
    (∑ U ∈ univ.filter (fun U : Submodule K V => U ≤ W), (X : Polynomial ℤ)^(finrank K U)) =
      projectiveRankEnumerator K W := by
  rw [sum_subspaces_contained]
  apply sum_congr rfl
  intro U _
  rw [← (Submodule.equivMapOfInjective W.subtype W.subtype_injective U).finrank_eq]

theorem spanZ_decomposition_of_projective (W : Submodule K V) (hW : W ≠ ⊤)
    (hP : ∀ U : Submodule K V, projectiveP K (V ⧸ U) = 1) :
    spanZ W hW = spanP W hW + projectiveRankEnumerator K V - projectiveRankEnumerator K W := by
  have hsum : spanZ W hW =
      ∑ F : FlatSpan W, ((X : Polynomial ℤ)^(spanRank W F) +
        if F = ⊥ then spanP W hW - 1 else 0) := by
    rw [spanZ, zKernel_apply, span_interval_univ]
    apply sum_congr rfl
    intro F _
    simp only [spanRank_bot, Nat.sub_zero]
    by_cases hF : F = ⊥
    · subst F
      simp [spanP]
    · have hU : ¬ F.1 ≤ W := F.2.resolve_left (fun h => hF (Subtype.ext h))
      have he : F = (⟨F.1, Or.inr hU⟩ : FlatSpan W) := rfl
      rw [he, upper_kl_projective W F.1 hW hU, hP F.1, mul_one, ite_eq_right hF, add_zero]
  rw [hsum, sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, ite_true]
  change (∑ F : FlatSpan W, (X : Polynomial ℤ)^(finrank K F.1)) + (spanP W hW - 1) = _
  rw [sum_flatSpan W (fun U : Submodule K V => (X : Polynomial ℤ)^(finrank K U))]
  simp only [finrank_bot, pow_zero]
  have hs := sum_filter_add_sum_filter_not (s := (univ : Finset (Submodule K V)))
    (fun U => U ≤ W) (fun U => (X : Polynomial ℤ)^(finrank K U))
  rw [subspace_contained_rank_sum W] at hs
  change projectiveRankEnumerator K W + _ = projectiveRankEnumerator K V at hs
  linear_combination hs

theorem spanZ_decomposition (W : Submodule K V) (hW : W ≠ ⊤) :
    spanZ W hW = spanP W hW + projectiveRankEnumerator K V - projectiveRankEnumerator K W :=
  spanZ_decomposition_of_projective W hW (fun U => projectiveP_eq_one K (V ⧸ U))

end BoseBurton
