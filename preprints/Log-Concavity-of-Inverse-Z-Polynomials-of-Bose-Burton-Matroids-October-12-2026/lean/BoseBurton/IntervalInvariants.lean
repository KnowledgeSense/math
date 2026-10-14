import BoseBurton.ActualInvariant
import BoseBurton.UpperIntervals
import BoseBurton.LowerIntervals

noncomputable section
namespace BoseBurton
open Submodule Module MatroidInverseZ
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

theorem upper_kl_projective (W U : Submodule K V) (hW : W ≠ ⊤) (hU : ¬ U ≤ W) :
    kl (spanRank W) (spanTop W hW) ⟨U, Or.inr hU⟩ = projectiveP K (V ⧸ U) := by
  classical
  have h := kl_interval_transport (quotientFlatEmbedding W U hU)
    (quotientFlatEmbedding_fills W U hU)
    (fun S : Submodule K (V ⧸ U) => finrank K S) (spanRank W)
    (quotientFlatEmbedding_rank_sub W U hU) ⊥ ⊤
  have hb : quotientFlatEmbedding W U hU ⊥ = ⟨U, Or.inr hU⟩ :=
    Subtype.ext (quotientFlatEmbedding_bot W U hU)
  have ht : quotientFlatEmbedding W U hU ⊤ = spanTop W hW :=
    Subtype.ext (quotientFlatEmbedding_top W U hU)
  rw [hb, ht] at h
  exact h

theorem upper_inverseZ_projective (W U : Submodule K V) (hW : W ≠ ⊤) (hU : ¬ U ≤ W) :
    inverseZ (spanRank W) ⟨U, Or.inr hU⟩ (spanTop W hW) = projectiveY K (V ⧸ U) := by
  classical
  have h := inverseZ_interval_transport (quotientFlatEmbedding W U hU)
    (quotientFlatEmbedding_fills W U hU)
    (fun S : Submodule K (V ⧸ U) => finrank K S) (spanRank W)
    (quotientFlatEmbedding_rank_sub W U hU) ⊥ ⊤
  have hb : quotientFlatEmbedding W U hU ⊥ = ⟨U, Or.inr hU⟩ :=
    Subtype.ext (quotientFlatEmbedding_bot W U hU)
  have ht : quotientFlatEmbedding W U hU ⊤ = spanTop W hW :=
    Subtype.ext (quotientFlatEmbedding_top W U hU)
  rw [hb, ht] at h
  exact h

omit [Module.Finite K V] [Finite V] in
theorem restricted_deleted_subspace_proper (W U : Submodule K V) (hU : ¬ U ≤ W) :
    W.comap U.subtype ≠ ⊤ := by
  intro h
  apply hU
  intro u hu
  have hh : (⟨u, hu⟩ : U) ∈ W.comap U.subtype := by rw [h]; trivial
  exact hh

omit [Module.Finite K V] [Finite V] in
theorem restrictionFlatEmbedding_top (W U : Submodule K V) (hU : ¬ U ≤ W) :
    restrictionFlatEmbedding W U
      (spanTop (W.comap U.subtype) (restricted_deleted_subspace_proper W U hU)) =
        ⟨U, Or.inr hU⟩ := by
  apply Subtype.ext
  change (⊤ : Submodule K U).map U.subtype = U
  rw [Submodule.map_top, Submodule.range_subtype]

omit [Module.Finite K V] in
theorem lower_kl_restriction (W U : Submodule K V) (hU : ¬ U ≤ W) :
    kl (spanRank W) ⟨U, Or.inr hU⟩ ⊥ =
      spanP (W.comap U.subtype) (restricted_deleted_subspace_proper W U hU) := by
  classical
  have h := kl_interval_transport (restrictionFlatEmbedding W U)
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

end BoseBurton
