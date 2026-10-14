import BoseBurton.QuotientRanks

noncomputable section
namespace BoseBurton
open Submodule Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Restriction to a surviving subspace is the same Bose–Burton construction inside it. -/
def restrictionFlatEmbedding (W U : Submodule K V) :
    FlatSpan (W.comap U.subtype) ↪o FlatSpan W where
  toFun S := ⟨S.1.map U.subtype, by
    rcases S.2 with h | h
    · exact Or.inl (by rw [h, Submodule.map_bot])
    · exact Or.inr (fun hh => h (Submodule.map_le_iff_le_comap.mp hh))⟩
  inj' := by
    intro S T h
    exact Subtype.ext (Submodule.map_injective_of_injective U.subtype_injective (congrArg Subtype.val h))
  map_rel_iff' := by
    intro S T
    exact Submodule.map_le_map_iff_of_injective U.subtype_injective S.1 T.1

theorem restrictionFlatEmbedding_fills (W U : Submodule K V)
    (A B : FlatSpan (W.comap U.subtype)) (F : FlatSpan W)
    (_hA : restrictionFlatEmbedding W U A ≤ F)
    (hB : F ≤ restrictionFlatEmbedding W U B) :
    ∃ S, restrictionFlatEmbedding W U S = F := by
  have hFU : F.1 ≤ U := by
    intro v hv
    have hh : v ∈ B.1.map U.subtype := hB hv
    obtain ⟨u, _, rfl⟩ := hh
    exact u.2
  have he : (F.1.comap U.subtype).map U.subtype = F.1 := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hFU]
  have hvalid : F.1.comap U.subtype = ⊥ ∨ ¬ F.1.comap U.subtype ≤ W.comap U.subtype := by
    rcases F.2 with h | h
    · left
      rw [h]
      exact LinearMap.ker_eq_bot.mpr U.subtype_injective
    · right
      intro hh
      exact h (he ▸ Submodule.map_le_iff_le_comap.mpr hh)
  exact ⟨⟨F.1.comap U.subtype, hvalid⟩, Subtype.ext he⟩

@[simp] theorem restrictionFlatEmbedding_bot (W U : Submodule K V) :
    restrictionFlatEmbedding W U ⊥ = ⊥ := by
  apply Subtype.ext
  change (⊥ : Submodule K U).map U.subtype = ⊥
  exact Submodule.map_bot (f := U.subtype)

theorem restrictionFlatEmbedding_rank (W U : Submodule K V)
    (S : FlatSpan (W.comap U.subtype)) :
    finrank K (restrictionFlatEmbedding W U S).1 = finrank K S.1 :=
  (Submodule.equivMapOfInjective U.subtype U.subtype_injective S.1).finrank_eq.symm

end BoseBurton
