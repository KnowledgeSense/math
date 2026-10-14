import BoseBurton.QuotientRanks

noncomputable section
namespace BoseBurton
open Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Above a surviving nonempty flat, every quotient direction survives. -/
def quotientFlatEmbedding (W U : Submodule K V) (hU : ¬ U ≤ W) :
    Submodule K (V ⧸ U) ↪o FlatSpan W where
  toFun S := ⟨S.comap U.mkQ, Or.inr (fun h => hU ((le_comap_mkQ U S).trans h))⟩
  inj' := by
    intro S T h
    exact Submodule.comap_injective_of_surjective U.mkQ_surjective
      (congrArg (fun F : FlatSpan W => F.1) h)
  map_rel_iff' := by
    intro S T
    exact U.comapMkQOrderEmbedding.le_iff_le

/-- No ambient flat is omitted between two flats in this quotient embedding. -/
theorem quotientFlatEmbedding_fills (W U : Submodule K V) (hU : ¬ U ≤ W)
    (A B : Submodule K (V ⧸ U)) (F : FlatSpan W)
    (hA : quotientFlatEmbedding W U hU A ≤ F)
    (_hB : F ≤ quotientFlatEmbedding W U hU B) :
    ∃ S, quotientFlatEmbedding W U hU S = F := by
  have hUF : U ≤ F.1 := (le_comap_mkQ U A).trans hA
  refine ⟨F.1.map U.mkQ, ?_⟩
  apply Subtype.ext
  change (F.1.map U.mkQ).comap U.mkQ = F.1
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hUF]

@[simp] theorem quotientFlatEmbedding_bot (W U : Submodule K V) (hU : ¬ U ≤ W) :
    (quotientFlatEmbedding W U hU ⊥).1 = U := by
  change (⊥ : Submodule K (V ⧸ U)).comap U.mkQ = U
  exact U.ker_mkQ

@[simp] theorem quotientFlatEmbedding_top (W U : Submodule K V) (hU : ¬ U ≤ W) :
    (quotientFlatEmbedding W U hU ⊤).1 = ⊤ := Submodule.comap_top _

variable [Module.Finite K V]

theorem quotientFlatEmbedding_rank (W U : Submodule K V) (hU : ¬ U ≤ W)
    (S : Submodule K (V ⧸ U)) :
    finrank K (quotientFlatEmbedding W U hU S).1 = finrank K S + finrank K U :=
  finrank_comap_mkQ U S

theorem quotientFlatEmbedding_rank_sub (W U : Submodule K V) (hU : ¬ U ≤ W)
    (S T : Submodule K (V ⧸ U)) :
    finrank K (quotientFlatEmbedding W U hU T).1 -
      finrank K (quotientFlatEmbedding W U hU S).1 = finrank K T - finrank K S :=
  finrank_comap_mkQ_sub U S T

end BoseBurton
