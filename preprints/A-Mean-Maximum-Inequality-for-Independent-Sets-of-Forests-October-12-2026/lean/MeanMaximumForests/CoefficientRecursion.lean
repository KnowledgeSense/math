import MeanMaximumForests.IndependenceCoefficients

namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
theorem independentSetCoefficient_mono {s t : Finset V} (hst : s ⊆ t) (k : ℕ) :
    independentSetCoefficient G s k ≤ independentSetCoefficient G t k := by
  classical
  apply card_le_card
  intro J hJ
  obtain ⟨hJ, hc⟩ := mem_filter.mp hJ
  obtain ⟨hJs, hJi⟩ := (mem_independentSetsWithin G).mp hJ
  exact mem_filter.mpr ⟨(mem_independentSetsWithin G).mpr ⟨hJs.trans hst, hJi⟩, hc⟩

/-- The deletion/closed-neighborhood recurrence, coefficient by coefficient. -/
theorem independentSetCoefficient_recursion (s : Finset V) (r : V) (hr : r ∈ s) (k : ℕ) :
    independentSetCoefficient G s (k + 1) =
      independentSetCoefficient G (s.erase r) (k + 1) +
        independentSetCoefficient G (compatibleVertices G s r) k := by
  classical
  unfold independentSetCoefficient
  rw [independentSetsWithin_decomposition G s r hr, filter_union,
    card_union_of_disjoint ((independent_decomposition_disjoint G s r).mono
      (filter_subset _ _) (filter_subset _ _)), filter_image]
  have he : (independentSetsWithin G (compatibleVertices G s r)).filter
      (fun J => (insert r J).card = k + 1) =
      (independentSetsWithin G (compatibleVertices G s r)).filter (fun J => J.card = k) := by
    apply filter_congr
    intro J hJ
    have hnot : r ∉ J := fun hrJ => compatible_not_mem G s r
      (((mem_independentSetsWithin G).mp hJ).1 hrJ)
    rw [card_insert_of_notMem hnot, Nat.add_right_cancel_iff]
  rw [he, card_image_of_injOn]
  exact (insert_injective_on_compatible G s r).mono (filter_subset _ _)

end MeanMaximumForests
