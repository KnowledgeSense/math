import MeanMaximumForests.GraphInvariants

namespace MeanMaximumForests
open Finset
variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

omit [Fintype V] [Fintype W] in
/-- Independent sets are preserved by graph isomorphisms. -/
theorem independent_map_iso (e : G ≃g H) (s : Finset V) :
    Independent H (s.map e.toEquiv.toEmbedding) ↔ Independent G s := by
  constructor
  · intro h u hu v hv huv
    exact h (e u) (mem_map.mpr ⟨u, hu, rfl⟩) (e v) (mem_map.mpr ⟨v, hv, rfl⟩)
      (e.map_adj_iff.mpr huv)
  · intro h u hu v hv huv
    obtain ⟨u₀, hu₀, eu⟩ := mem_map.mp hu
    obtain ⟨v₀, hv₀, ev⟩ := mem_map.mp hv
    subst u
    subst v
    exact h u₀ hu₀ v₀ hv₀ (e.map_adj_iff.mp huv)

theorem independentSets_iso [DecidableEq W] (e : G ≃g H) :
    independentSetsWithin H univ =
      (independentSetsWithin G univ).image (Finset.map e.toEquiv.toEmbedding) := by
  classical
  ext t
  simp only [mem_image, mem_independentSetsWithin, subset_univ, true_and]
  constructor
  · intro ht
    refine ⟨t.map e.symm.toEquiv.toEmbedding, (independent_map_iso e.symm t).mpr ht, ?_⟩
    ext w
    simp only [mem_map]
    constructor
    · rintro ⟨v, ⟨w', hw', hve⟩, hwe⟩
      subst v
      have hew : w' = w := by simpa using hwe
      exact hew ▸ hw'
    · intro hw
      exact ⟨e.symm w, ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩
  · rintro ⟨s, hs, rfl⟩
    exact (independent_map_iso e s).mpr hs

theorem independentSetCount_iso (e : G ≃g H) :
    independentSetCount H univ = independentSetCount G univ := by
  classical
  unfold independentSetCount
  rw [independentSets_iso e, card_image_of_injective _ (map_injective _)]

theorem independentSetSizeSum_iso (e : G ≃g H) :
    independentSetSizeSum H univ = independentSetSizeSum G univ := by
  classical
  unfold independentSetSizeSum
  rw [independentSets_iso e, sum_image (map_injective _).injOn]
  simp

theorem graphMean_iso (e : G ≃g H) : graphMean H = graphMean G := by
  unfold graphMean meanIndependentSetSize
  rw [independentSetCount_iso e, independentSetSizeSum_iso e]

omit [Fintype V] in
theorem indepNum_le_iso (e : G ≃g H) : G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hi := (independent_iff_isIndepSet G s).mpr hs.isIndepSet
  have hi' := (independent_map_iso e s).mpr hi
  have hc := ((independent_iff_isIndepSet H _).mp hi').card_le_indepNum
  simpa [hs.card_eq] using hc

theorem indepNum_iso (e : G ≃g H) : H.indepNum = G.indepNum :=
  le_antisymm (indepNum_le_iso e.symm) (indepNum_le_iso e)

end MeanMaximumForests
