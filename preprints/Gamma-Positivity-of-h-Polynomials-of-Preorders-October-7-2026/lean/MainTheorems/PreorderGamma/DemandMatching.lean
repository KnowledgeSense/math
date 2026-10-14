import MainTheorems.PreorderGamma.Bipartite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

abbrev DemandCells (d : L → ℕ) := Σ a : L, Fin (d a)

omit [Fintype L] in
theorem demand_iff_cell_transversal (r : L → R → Prop) (d : L → ℕ) :
    IsDemand r d ↔ HasTransversal (fun c : DemandCells d => r c.1) := by
  classical
  constructor
  · intro hd
    apply (hasTransversal_iff_hall _).mpr
    intro s
    let p := s.image Sigma.fst
    have hs : s ⊆ p.sigma (fun a => (Finset.univ : Finset (Fin (d a)))) := by
      intro c hc
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_image.mpr ⟨c, hc, rfl⟩, Finset.mem_univ _⟩
    have hcard : s.card ≤ ∑ a ∈ p, d a := by
      have h := Finset.card_le_card hs
      simpa [Finset.card_sigma] using h
    have hn : graphNeighbors (fun c : DemandCells d => r c.1) s =
        graphNeighbors r p := by
      ext b
      constructor
      · intro hb
        obtain ⟨c, hc, hcb⟩ := mem_graphNeighbors.mp hb
        exact mem_graphNeighbors.mpr
          ⟨c.1, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hcb⟩
      · intro hb
        obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
        obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
        exact mem_graphNeighbors.mpr ⟨c, hc, hca.symm ▸ hab⟩
    rw [hn]
    exact hcard.trans (hd p)
  · rintro ⟨f, hf, hrel⟩ s
    let c := s.sigma (fun a => (Finset.univ : Finset (Fin (d a))))
    have hsub : c.image f ⊆ graphNeighbors r s := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact mem_graphNeighbors.mpr ⟨a.1, (Finset.mem_sigma.mp ha).1, hrel a⟩
    calc
      ∑ a ∈ s, d a = c.card := by simp [c, Finset.card_sigma]
      _ = (c.image f).card := (Finset.card_image_of_injective c hf).symm
      _ ≤ (graphNeighbors r s).card := Finset.card_le_card hsub

end ResearchMain.PreorderGamma
