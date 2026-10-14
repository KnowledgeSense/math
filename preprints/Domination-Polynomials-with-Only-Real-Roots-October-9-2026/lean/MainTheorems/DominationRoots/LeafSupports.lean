import MainTheorems.DominationRoots.GraphTrace

namespace ResearchMain.DominationRoots

open Classical ResearchMain.Domination

variable {V : Type*} [Fintype V]

theorem nonisolated_neighbor {G : SimpleGraph V} {v : V} (hv : v ∉ isolatedVertices G) :
    ∃ u, G.Adj v u := by
  have hnot : ¬closedNeighborhood G v ⊆ {v} := by
    intro h
    apply hv
    apply (mem_isolatedVertices G v).mpr
    exact Finset.Subset.antisymm h (by simpa using self_mem_closedNeighborhood G v)
  obtain ⟨u, hu, hne⟩ := Finset.not_subset.mp hnot
  have hneq : u ≠ v := by simpa using hne
  exact ⟨u, ((mem_closedNeighborhood G u v).mp hu).resolve_left hneq |>.symm⟩

theorem unsupported_vertex_deletion {G : SimpleGraph V} {v : V}
    (hv : v ∉ isolatedVertices G)
    (hunsupported : ∀ u ∈ selectedLeaves G, ¬G.Adj v u) :
    Dominates G ((Finset.univ \ selectedLeaves G).erase v) := by
  intro w
  by_cases hw : w ∈ selectedLeaves G
  · obtain ⟨u, hu⟩ := leaf_neighbor_exists (selectedLeaf_card hw)
    have hun : u ∉ selectedLeaves G := fun h => selectedLeaves_not_adjacent hw h hu
    have huv : u ≠ v := by
      intro he
      subst u
      exact hunsupported w hw hu.symm
    exact ⟨u, by simp [hun, huv], Or.inr hu.symm⟩
  · by_cases hwv : w = v
    · subst w
      obtain ⟨u, hu⟩ := nonisolated_neighbor hv
      have hun : u ∉ selectedLeaves G := fun h => hunsupported u h hu
      exact ⟨u, by simp [hun, hu.ne.symm], Or.inr hu.symm⟩
    · exact ⟨w, by simp [hw, hwv], Or.inl rfl⟩

theorem every_core_vertex_supported {G : SimpleGraph V}
    (hmin : dominationNumber G = Fintype.card V - (leafNeighborhoods G).card)
    {v : V} (hv : v ∉ isolatedVertices G) (hn : v ∉ selectedLeaves G) :
    ∃ u ∈ selectedLeaves G, G.Adj v u := by
  by_contra h
  push Not at h
  have hdom := unsupported_vertex_deletion hv h
  have hbound := dominationNumber_le G _ hdom
  have hmem : v ∈ Finset.univ \ selectedLeaves G := by simp [hn]
  have hcard : ((Finset.univ \ selectedLeaves G).erase v).card + 1 = dominationNumber G := by
    rw [Finset.card_erase_add_one hmem, complement_card, selectedLeaves_card, hmin]
  omega

noncomputable def coreVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ \ (selectedLeaves G ∪ isolatedVertices G)

noncomputable def attachedLeaves (G : SimpleGraph V) (v : V) : Finset V :=
  (selectedLeaves G).filter (G.Adj v)

theorem core_leaf_nonempty {G : SimpleGraph V}
    (hmin : dominationNumber G = Fintype.card V - (leafNeighborhoods G).card)
    {v : V} (hv : v ∈ coreVertices G) : (attachedLeaves G v).Nonempty := by
  have h := Finset.mem_sdiff.mp hv |>.2
  have hn : v ∉ selectedLeaves G := fun hv => h (Finset.mem_union_left _ hv)
  have hi : v ∉ isolatedVertices G := fun hv => h (Finset.mem_union_right _ hv)
  obtain ⟨u, hu, hadj⟩ := every_core_vertex_supported hmin hi hn
  exact ⟨u, Finset.mem_filter.mpr ⟨hu, hadj⟩⟩

theorem selected_leaf_unique_neighbor {G : SimpleGraph V} {u v w : V}
    (hu : u ∈ selectedLeaves G) (hv : G.Adj u v) (hw : G.Adj u w) : v = w := by
  have he := closedNeighborhood_pair (selectedLeaf_card hu)
    ((mem_closedNeighborhood G v u).mpr (Or.inr hv.symm)) hv.ne
  have hm := (mem_closedNeighborhood G w u).mpr (Or.inr hw.symm)
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.resolve_left hw.ne.symm |>.symm

theorem selected_leaf_neighbor_core {G : SimpleGraph V} {u v : V}
    (hu : u ∈ selectedLeaves G) (hv : G.Adj u v) : v ∈ coreVertices G := by
  unfold coreVertices
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
  constructor
  · exact fun h => selectedLeaves_not_adjacent hu h hv
  · intro h
    have he := (mem_isolatedVertices G v).mp h
    have hm := (mem_closedNeighborhood G u v).mpr (Or.inr hv)
    rw [he, Finset.mem_singleton] at hm
    exact hv.ne hm

end ResearchMain.DominationRoots
