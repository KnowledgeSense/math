import MainTheorems.PreorderGamma.SurplusHall
import MainTheorems.PreorderGamma.Bipartite

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

omit [Fintype E] in
theorem restricted_neighbors_image (z j : Finset E) (s : Finset j) :
    (graphNeighbors (fun a : j => fun b : z => (b : E) ≤ (a : E)) s).image
      Subtype.val = neighborhood z (s.image Subtype.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
    exact mem_neighborhood.mpr
      ⟨b.property, a.val, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hab⟩
  · intro he
    obtain ⟨hez, a, ha, hea⟩ := mem_neighborhood.mp he
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨⟨e, hez⟩, ?_, rfl⟩
    exact mem_graphNeighbors.mpr ⟨b, hb, hba.symm ▸ hea⟩

omit [Fintype E] in
theorem restricted_neighbors_card (z j : Finset E) (s : Finset j) :
    (graphNeighbors (fun a : j => fun b : z => (b : E) ≤ (a : E)) s).card =
      (neighborhood z (s.image Subtype.val)).card := by
  classical
  rw [← restricted_neighbors_image z j s]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

omit [Fintype E] in
theorem restrictedDemand_iff_subsetHall (z j : Finset E) (d : E → ℕ) :
    IsDemand (fun a : j => fun b : z => (b : E) ≤ (a : E)) (fun a => d a.val) ↔
      ∀ s : Finset E, s ⊆ j → ∑ a ∈ s, d a ≤ (neighborhood z s).card := by
  classical
  constructor
  · intro hd s hs
    let t : Finset j := Finset.univ.filter fun a => a.val ∈ s
    have ht : t.image Subtype.val = s := by
      ext a
      constructor
      · intro ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hb).2
      · intro ha
        exact Finset.mem_image.mpr
          ⟨⟨a, hs ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
    have h := hd t
    rw [restricted_neighbors_card, ht] at h
    have hsum : ∑ a ∈ s, d a = ∑ a ∈ t, d a.val := by
      rw [← ht, Finset.sum_image]
      intro a ha b hb hab
      exact Subtype.ext hab
    rwa [hsum]
  · intro hd s
    have hs : s.image Subtype.val ⊆ j := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact b.property
    have h := hd (s.image Subtype.val) hs
    rw [← restricted_neighbors_card z j s] at h
    rw [Finset.sum_image] at h
    · exact h
    · intro a ha b hb hab
      exact Subtype.ext hab

theorem lattice_surplus_isDemand {x : E → ℕ} (hx : IsLatticePoint x) :
    IsDemand (fun a : highSet x => fun b : zeroSet x => (b : E) ≤ (a : E))
      (fun a => x a.val - 1) := by
  classical
  intro s
  have hs : s.image Subtype.val ⊆ highSet x := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact b.property
  have h := (isLatticePoint_iff_surplusHall x).mp hx (s.image Subtype.val) hs
  rw [← restricted_neighbors_card (zeroSet x) (highSet x) s] at h
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    exact Subtype.ext hab

end ResearchMain.PreorderGamma
