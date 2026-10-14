import Mathlib.Combinatorics.Enumerative.Composition
import MainTheorems.Domination.Compositions

namespace ResearchMain.Domination

open Classical

def compositionSetEquiv (n : ℕ) : Composition (n + 1) ≃ Finset (Fin n) :=
  (compositionEquiv (n + 1)).trans (compositionAsSetEquiv (n + 1))

def selectedVertices {n : ℕ} (c : Composition (n + 1)) : Finset (Fin n) :=
  compositionSetEquiv n c

theorem mem_selectedVertices {n : ℕ} (c : Composition (n + 1)) (v : Fin n) :
    v ∈ selectedVertices c ↔
      (⟨v.val + 1, by omega⟩ : Fin (n + 2)) ∈ c.boundaries := by
  simp [selectedVertices, compositionSetEquiv, compositionEquiv,
    compositionAsSetEquiv, Composition.toCompositionAsSet, add_comm]

def internalVertexEmbedding (n : ℕ) : Fin n ↪ Fin (n + 2) where
  toFun v := ⟨v.val + 1, by omega⟩
  inj' := by
    intro v w h
    apply Fin.ext
    have heq := congrArg Fin.val h
    dsimp only at heq
    omega

@[simp] theorem internalVertexEmbedding_val (n : ℕ) (v : Fin n) :
    (internalVertexEmbedding n v).val = v.val + 1 := rfl

theorem selected_boundaries {n : ℕ} (c : Composition (n + 1)) :
    c.boundaries = insert 0 (insert (Fin.last (n + 1))
      ((selectedVertices c).map (internalVertexEmbedding n))) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · by_cases hvlast : v = Fin.last (n + 1)
      · exact Or.inr (Or.inl hvlast)
      · have hvpos : 1 ≤ v.val := by
          have hne : v.val ≠ 0 := by intro h; exact hv0 (Fin.ext h)
          omega
        have hvlt : v.val < n + 1 := by
          have hne : v.val ≠ n + 1 := by intro h; exact hvlast (Fin.ext h)
          have := v.isLt
          omega
        let u : Fin n := ⟨v.val - 1, by omega⟩
        have hu : internalVertexEmbedding n u = v := by
          apply Fin.ext
          rw [internalVertexEmbedding_val]
          change v.val - 1 + 1 = v.val
          exact Nat.sub_add_cancel hvpos
        refine Or.inr (Or.inr ⟨u, ?_, hu⟩)
        apply (mem_selectedVertices c u).mpr
        change internalVertexEmbedding n u ∈ c.boundaries
        rw [hu]
        exact hv
  · rintro (rfl | rfl | ⟨u, hu, rfl⟩)
    · exact c.toCompositionAsSet.zero_mem
    · exact c.toCompositionAsSet.getLast_mem
    · exact (mem_selectedVertices c u).mp hu

theorem selectedVertices_card {n : ℕ} (c : Composition (n + 1)) :
    (selectedVertices c).card + 1 = c.length := by
  have hzero : (0 : Fin (n + 2)) ∉ (selectedVertices c).map (internalVertexEmbedding n) := by
    intro h
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp h
    have := congrArg Fin.val hv
    simp only [internalVertexEmbedding_val, Fin.val_zero] at this
    omega
  have hlast : Fin.last (n + 1) ∉ (selectedVertices c).map (internalVertexEmbedding n) := by
    intro h
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp h
    have := congrArg Fin.val hv
    simp only [internalVertexEmbedding_val, Fin.val_last] at this
    have := v.isLt
    omega
  have hzero' : (0 : Fin (n + 2)) ∉ insert (Fin.last (n + 1))
      ((selectedVertices c).map (internalVertexEmbedding n)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by intro h; have := congrArg Fin.val h; simp at this, hzero⟩
  have hcard := c.card_boundaries_eq_succ_length
  rw [selected_boundaries, Finset.card_insert_of_notMem hzero',
    Finset.card_insert_of_notMem hlast, Finset.card_map] at hcard
  omega

end ResearchMain.Domination
