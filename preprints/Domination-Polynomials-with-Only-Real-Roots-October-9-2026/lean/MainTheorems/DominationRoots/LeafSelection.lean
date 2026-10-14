import MainTheorems.DominationRoots.DominationNumber

namespace ResearchMain.DominationRoots

open Classical ResearchMain.Domination

variable {V : Type*} [Fintype V]

noncomputable def leafRepresentative (G : SimpleGraph V) (R : ↥(leafNeighborhoods G)) : V :=
  ((mem_leafNeighborhoods G R.val).mp R.property).choose

theorem leafRepresentative_neighborhood (G : SimpleGraph V) (R : ↥(leafNeighborhoods G)) :
    closedNeighborhood G (leafRepresentative G R) = R.val :=
  ((mem_leafNeighborhoods G R.val).mp R.property).choose_spec.1

theorem leafRepresentative_card (G : SimpleGraph V) (R : ↥(leafNeighborhoods G)) :
    (closedNeighborhood G (leafRepresentative G R)).card = 2 := by
  rw [leafRepresentative_neighborhood]
  exact ((mem_leafNeighborhoods G R.val).mp R.property).choose_spec.2

theorem leafRepresentative_injective (G : SimpleGraph V) :
    Function.Injective (leafRepresentative G) := by
  intro R S h
  apply Subtype.ext
  rw [← leafRepresentative_neighborhood G R, ← leafRepresentative_neighborhood G S, h]

noncomputable def selectedLeaves (G : SimpleGraph V) : Finset V :=
  Finset.univ.image (leafRepresentative G)

theorem selectedLeaves_card (G : SimpleGraph V) :
    (selectedLeaves G).card = (leafNeighborhoods G).card := by
  rw [selectedLeaves, Finset.card_image_of_injective _ (leafRepresentative_injective G),
    Finset.card_univ, Fintype.card_coe]

theorem selectedLeaf_card {G : SimpleGraph V} {v : V} (hv : v ∈ selectedLeaves G) :
    (closedNeighborhood G v).card = 2 := by
  obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hv
  exact leafRepresentative_card G R

theorem closedNeighborhood_pair {G : SimpleGraph V} {v u : V}
    (hc : (closedNeighborhood G v).card = 2) (hu : u ∈ closedNeighborhood G v)
    (hne : v ≠ u) : closedNeighborhood G v = {v, u} := by
  have hsub : {v, u} ⊆ closedNeighborhood G v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨self_mem_closedNeighborhood G v, hu⟩
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair hne, hc])).symm

theorem leaf_neighbor_exists {G : SimpleGraph V} {v : V}
    (hc : (closedNeighborhood G v).card = 2) : ∃ u, G.Adj v u := by
  have hnot : ¬closedNeighborhood G v ⊆ {v} := by
    intro h
    have he := Finset.card_le_card h
    rw [hc, Finset.card_singleton] at he
    omega
  obtain ⟨u, hu, hne⟩ := Finset.not_subset.mp hnot
  have hneq : u ≠ v := by simpa using hne
  exact ⟨u, ((mem_closedNeighborhood G u v).mp hu).resolve_left hneq |>.symm⟩

theorem selectedLeaves_not_adjacent {G : SimpleGraph V} {v u : V}
    (hv : v ∈ selectedLeaves G) (hu : u ∈ selectedLeaves G) : ¬G.Adj v u := by
  intro h
  have hvu : v ≠ u := h.ne
  have hvpair := closedNeighborhood_pair (selectedLeaf_card hv)
    ((mem_closedNeighborhood G u v).mpr (Or.inr h.symm)) hvu
  have hupair := closedNeighborhood_pair (selectedLeaf_card hu)
    ((mem_closedNeighborhood G v u).mpr (Or.inr h)) (Ne.symm hvu)
  obtain ⟨R, _, hR⟩ := Finset.mem_image.mp hv
  obtain ⟨S, _, hS⟩ := Finset.mem_image.mp hu
  have he : R = S := by
    apply Subtype.ext
    rw [← leafRepresentative_neighborhood G R, ← leafRepresentative_neighborhood G S,
      hR, hS, hvpair, hupair, Finset.pair_comm]
  exact hvu (hR.symm.trans ((congrArg (leafRepresentative G) he).trans hS))

theorem selectedLeaves_complement_dominates (G : SimpleGraph V) :
    Dominates G (Finset.univ \ selectedLeaves G) := by
  intro v
  by_cases hv : v ∈ selectedLeaves G
  · obtain ⟨u, hu⟩ := leaf_neighbor_exists (selectedLeaf_card hv)
    refine ⟨u, ?_, Or.inr hu.symm⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => selectedLeaves_not_adjacent hv h hu
  · exact ⟨v, by simp [hv], Or.inl rfl⟩

theorem dominationNumber_le_leaf_bound (G : SimpleGraph V) :
    dominationNumber G ≤ Fintype.card V - (leafNeighborhoods G).card := by
  have h := dominationNumber_le G _ (selectedLeaves_complement_dominates G)
  simpa only [complement_card, selectedLeaves_card] using h

end ResearchMain.DominationRoots
