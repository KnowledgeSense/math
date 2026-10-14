import MainTheorems.DominationRoots.DeletionCounts

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

theorem deletedDominatingSets_two (G : SimpleGraph V) :
    deletedDominatingSets G 2 =
      (Finset.univ \ isolatedVertices G).powersetCard 2 \ leafNeighborhoods G := by
  ext R
  rw [mem_deletedDominatingSets, Finset.mem_sdiff, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hc, hd⟩
    have hsub : R ⊆ Finset.univ \ isolatedVertices G := by
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hi
      apply (not_dominates_complement G R).mpr ?_ hd
      refine ⟨v, ?_⟩
      rw [(mem_isolatedVertices G v).mp hi]
      exact Finset.singleton_subset_iff.mpr hv
    exact ⟨⟨hsub, hc⟩, fun h => ((not_dominates_delete_pair G R hc hsub).mpr h) hd⟩
  · rintro ⟨⟨hsub, hc⟩, hnot⟩
    refine ⟨hc, ?_⟩
    by_contra hd
    exact hnot ((not_dominates_delete_pair G R hc hsub).mp hd)

theorem dominationCount_antepenultimate (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) :
    dominationCount G (Fintype.card V - 2) =
      Nat.choose (Fintype.card V - (isolatedVertices G).card) 2 - (leafNeighborhoods G).card := by
  rw [← deletedDominatingSets_card G 2 hn, deletedDominatingSets_two,
    Finset.card_sdiff_of_subset (leafNeighborhoods_subset G),
    Finset.card_powersetCard, complement_card]

theorem leafNeighborhoods_card_le_choose (G : SimpleGraph V) :
    (leafNeighborhoods G).card ≤ Nat.choose (Fintype.card V - (isolatedVertices G).card) 2 := by
  have h := Finset.card_le_card (leafNeighborhoods_subset G)
  simpa only [Finset.card_powersetCard, complement_card] using h

theorem dominationPolynomial_top_coefficients (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V) :
    (dominationPolynomial G).coeff (Fintype.card V) = 1 ∧
    (dominationPolynomial G).coeff (Fintype.card V - 1) =
      (Fintype.card V - (isolatedVertices G).card : ℕ) ∧
    (dominationPolynomial G).coeff (Fintype.card V - 2) =
      (Nat.choose (Fintype.card V - (isolatedVertices G).card) 2 : ℤ) -
        ((leafNeighborhoods G).card : ℤ) := by
  simp only [dominationPolynomial_coeff]
  constructor
  · rw [dominationCount_full]
    rfl
  constructor
  · rw [dominationCount_penultimate G (by omega)]
  · rw [dominationCount_antepenultimate G hn,
      Nat.cast_sub (leafNeighborhoods_card_le_choose G)]

end ResearchMain.DominationRoots
