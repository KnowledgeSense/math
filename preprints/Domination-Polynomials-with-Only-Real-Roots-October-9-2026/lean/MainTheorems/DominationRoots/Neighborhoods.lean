import MainTheorems.DominationRoots.Parity

namespace ResearchMain.DominationRoots

open Classical ResearchMain.Domination

variable {V : Type*} [Fintype V]

noncomputable def closedNeighborhood (G : SimpleGraph V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => u = v ∨ G.Adj u v)

theorem mem_closedNeighborhood (G : SimpleGraph V) (u v : V) :
    u ∈ closedNeighborhood G v ↔ u = v ∨ G.Adj u v := by
  simp [closedNeighborhood]

theorem self_mem_closedNeighborhood (G : SimpleGraph V) (v : V) :
    v ∈ closedNeighborhood G v := by simp [mem_closedNeighborhood]

theorem closedNeighborhood_symm {G : SimpleGraph V} {u v : V}
    (h : u ∈ closedNeighborhood G v) : v ∈ closedNeighborhood G u := by
  rcases (mem_closedNeighborhood G u v).mp h with rfl | h
  · exact self_mem_closedNeighborhood G u
  · exact (mem_closedNeighborhood G v u).mpr (Or.inr h.symm)

theorem not_dominates_complement (G : SimpleGraph V) (R : Finset V) :
    ¬Dominates G (Finset.univ \ R) ↔ ∃ v, closedNeighborhood G v ⊆ R := by
  simp only [Dominates, Finset.mem_sdiff, Finset.mem_univ, true_and,
    not_forall, not_exists, not_and]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro u hu
    by_contra hnot
    exact hv u hnot ((mem_closedNeighborhood G u v).mp hu)
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro u hu hdom
    exact hu (hv ((mem_closedNeighborhood G u v).mpr hdom))

noncomputable def isolatedVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => closedNeighborhood G v = {v})

theorem mem_isolatedVertices (G : SimpleGraph V) (v : V) :
    v ∈ isolatedVertices G ↔ closedNeighborhood G v = {v} := by
  simp [isolatedVertices]

theorem closedNeighborhood_singleton_iff (G : SimpleGraph V) (v : V) :
    (closedNeighborhood G v).card = 1 ↔ closedNeighborhood G v = {v} := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
    have hv := self_mem_closedNeighborhood G v
    rw [hu, Finset.mem_singleton] at hv
    simpa [hv] using hu
  · intro h
    simp [h]

noncomputable def leafNeighborhoods (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ.filter (fun v => (closedNeighborhood G v).card = 2)).image
    (closedNeighborhood G)

theorem mem_leafNeighborhoods (G : SimpleGraph V) (S : Finset V) :
    S ∈ leafNeighborhoods G ↔ ∃ v, closedNeighborhood G v = S ∧ S.card = 2 := by
  simp only [leafNeighborhoods, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨v, hcard, rfl⟩
    exact ⟨v, rfl, hcard⟩
  · rintro ⟨v, rfl, hcard⟩
    exact ⟨v, hcard, rfl⟩

theorem not_dominates_delete_one (G : SimpleGraph V) (v : V) :
    ¬Dominates G (Finset.univ \ {v}) ↔ v ∈ isolatedVertices G := by
  rw [not_dominates_complement, mem_isolatedVertices]
  constructor
  · rintro ⟨u, hu⟩
    have huv : u = v := Finset.mem_singleton.mp (hu (self_mem_closedNeighborhood G u))
    subst u
    exact Finset.Subset.antisymm hu (by simpa using self_mem_closedNeighborhood G v)
  · intro h
    exact ⟨v, h.le⟩

end ResearchMain.DominationRoots
