import Paving.HyperplaneCover
import Paving.ContainingSubsetCount

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset
variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The exact hyperplane partition remains a partition after fixing any
smaller subset. This is the pointwise identity needed in upper Möbius sums. -/
theorem IsPaving.pointed_hyperplane_packing (hM : IsPaving M) (hr : 1≤rank M)
    (A : Set α) (hAE : A ⊆ M.E) (hA : A.ncard≤rank M-1) :
    (∑ H ∈ hyperplanes M, if A ⊆ H then
      (H.ncard-A.ncard).choose (rank M-1-A.ncard) else 0) =
      (M.E.ncard-A.ncard).choose (rank M-1-A.ncard) := by
  classical
  let B := fun H : Set α => (H.toFinset.powersetCard (rank M-1)).filter
    (fun G => A.toFinset ⊆ G)
  have hd : ((hyperplanes M) : Set (Set α)).PairwiseDisjoint B := by
    intro H hH K hK hne
    exact (hM.hyperplane_blocks_disjoint hr ((mem_hyperplanes M H).mp hH)
      ((mem_hyperplanes M K).mp hK) hne).mono (filter_subset _ _) (filter_subset _ _)
  have he : (hyperplanes M).biUnion B =
      (M.E.toFinset.powersetCard (rank M-1)).filter (fun G => A.toFinset ⊆ G) := by
    rw [← hM.hyperplane_block_cover hr]
    ext S
    simp only [B, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨H,hH,hSH,hAS⟩
      exact ⟨⟨H,hH,hSH⟩,hAS⟩
    · rintro ⟨⟨H,hH,hSH⟩,hAS⟩
      exact ⟨H,hH,hSH,hAS⟩
  have hc := congrArg Finset.card he
  rw [card_biUnion hd, containing_subsets_card A.toFinset M.E.toFinset
    (by simpa only [Set.toFinset_subset_toFinset] using hAE) _
    (by simpa only [← Set.ncard_eq_toFinset_card'] using hA)] at hc
  have hB : ∀ H, (B H).card = if A ⊆ H then
      (H.ncard-A.ncard).choose (rank M-1-A.ncard) else 0 := by
    intro H
    dsimp only [B]
    rw [containing_subsets_card_ite A.toFinset H.toFinset _
      (by simpa only [← Set.ncard_eq_toFinset_card'] using hA)]
    simp only [Set.toFinset_subset_toFinset, ← Set.ncard_eq_toFinset_card']
  simpa only [hB, ← Set.ncard_eq_toFinset_card'] using hc

end Paving
