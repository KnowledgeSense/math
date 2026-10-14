import MainTheorems.DominationRoots.Neighborhoods

namespace ResearchMain.DominationRoots

open Classical ResearchMain.Domination

variable {V : Type*} [Fintype V]

noncomputable def deletedDominatingSets (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.powersetCard k |>.filter (fun R => Dominates G (Finset.univ \ R))

theorem mem_deletedDominatingSets (G : SimpleGraph V) (k : ℕ) (R : Finset V) :
    R ∈ deletedDominatingSets G k ↔ R.card = k ∧ Dominates G (Finset.univ \ R) := by
  simp [deletedDominatingSets, Finset.mem_powersetCard]

theorem complement_card (R : Finset V) :
    (Finset.univ \ R).card = Fintype.card V - R.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ]

theorem complement_complement (R : Finset V) :
    Finset.univ \ (Finset.univ \ R) = R := by
  ext v
  simp

theorem deletedDominatingSets_card (G : SimpleGraph V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    (deletedDominatingSets G k).card = dominationCount G (Fintype.card V - k) := by
  unfold dominationCount
  apply Finset.card_bij (fun R _ => Finset.univ \ R)
  · intro R hR
    obtain ⟨hc, hd⟩ := (mem_deletedDominatingSets G k R).mp hR
    exact (mem_dominatingSets G _ _).mpr ⟨by rw [complement_card, hc], hd⟩
  · intro R hR S hS he
    have h := congrArg (fun T : Finset V => Finset.univ \ T) he
    simpa only [complement_complement] using h
  · intro S hS
    obtain ⟨hc, hd⟩ := (mem_dominatingSets G _ S).mp hS
    refine ⟨Finset.univ \ S, ?_, complement_complement S⟩
    apply (mem_deletedDominatingSets G k _).mpr
    constructor
    · rw [complement_card, hc]
      omega
    · simpa only [complement_complement] using hd

theorem deletedDominatingSets_one (G : SimpleGraph V) :
    deletedDominatingSets G 1 =
      (Finset.univ \ isolatedVertices G).image (fun v => {v}) := by
  ext R
  rw [mem_deletedDominatingSets, Finset.mem_image]
  constructor
  · rintro ⟨hc, hd⟩
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨v, ?_, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => ((not_dominates_delete_one G v).mpr h) hd
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Finset.card_singleton v, ?_⟩
    by_contra hd
    exact (Finset.mem_sdiff.mp hv).2 ((not_dominates_delete_one G v).mp hd)

theorem dominationCount_penultimate (G : SimpleGraph V) (hn : 1 ≤ Fintype.card V) :
    dominationCount G (Fintype.card V - 1) =
      Fintype.card V - (isolatedVertices G).card := by
  rw [← deletedDominatingSets_card G 1 hn, deletedDominatingSets_one,
    Finset.card_image_of_injective _ Finset.singleton_injective, complement_card]

theorem closedNeighborhood_avoids_isolates {G : SimpleGraph V} {v : V}
    (hv : v ∉ isolatedVertices G) : closedNeighborhood G v ⊆ Finset.univ \ isolatedVertices G := by
  intro u hu
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro h
  have hi := (mem_isolatedVertices G u).mp h
  have hvu := closedNeighborhood_symm hu
  rw [hi, Finset.mem_singleton] at hvu
  exact hv (hvu ▸ h)

theorem leafNeighborhoods_subset (G : SimpleGraph V) :
    leafNeighborhoods G ⊆ (Finset.univ \ isolatedVertices G).powersetCard 2 := by
  intro R hR
  obtain ⟨v, rfl, hc⟩ := (mem_leafNeighborhoods G R).mp hR
  apply Finset.mem_powersetCard.mpr
  refine ⟨closedNeighborhood_avoids_isolates ?_, hc⟩
  intro h
  rw [(mem_isolatedVertices G v).mp h, Finset.card_singleton] at hc
  omega

theorem not_dominates_delete_pair (G : SimpleGraph V) (R : Finset V) (hc : R.card = 2)
    (hR : R ⊆ Finset.univ \ isolatedVertices G) :
    ¬Dominates G (Finset.univ \ R) ↔ R ∈ leafNeighborhoods G := by
  rw [not_dominates_complement, mem_leafNeighborhoods]
  constructor
  · rintro ⟨v, hv⟩
    have hvR := hv (self_mem_closedNeighborhood G v)
    have hn := (Finset.mem_sdiff.mp (hR hvR)).2
    have hle : (closedNeighborhood G v).card ≤ 2 := by
      simpa [hc] using Finset.card_le_card hv
    have h0 : 0 < (closedNeighborhood G v).card :=
      Finset.card_pos.mpr ⟨v, self_mem_closedNeighborhood G v⟩
    have hne : (closedNeighborhood G v).card ≠ 1 := by
      intro h
      exact hn ((mem_isolatedVertices G v).mpr ((closedNeighborhood_singleton_iff G v).mp h))
    have hcard : (closedNeighborhood G v).card = R.card := by omega
    exact ⟨v, Finset.eq_of_subset_of_card_le hv hcard.ge, hc⟩
  · rintro ⟨v, hv, _⟩
    exact ⟨v, hv.le⟩

end ResearchMain.DominationRoots
