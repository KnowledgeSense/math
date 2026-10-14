import Paving.HyperplanePacking
import Paving.HyperplaneIntervals

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem IsPaving.closure_isHyperplane (hM : IsPaving M) {S : Set α}
    (hSE : S ⊆ M.E) (hS : S.ncard+1=rank M) : IsHyperplane M (M.closure S) := by
  refine ⟨M.isFlat_closure S, ?_⟩
  change (M.eRk (M.closure S)).toNat+1=rank M
  rw [M.eRk_closure_eq, (hM.indep_of_card_lt hSE (by omega)).eRk_eq_encard]
  exact hS

/-- Every (rank−1)-subset of the ground set belongs to an actual hyperplane. -/
theorem IsPaving.exists_hyperplane_superset (hM : IsPaving M) {S : Set α}
    (hSE : S ⊆ M.E) (hS : S.ncard+1=rank M) :
    ∃ H, IsHyperplane M H ∧ S ⊆ H :=
  ⟨M.closure S, hM.closure_isHyperplane hSE hS, M.subset_closure S hSE⟩

theorem IsPaving.hyperplane_block_cover (hM : IsPaving M) (hr : 1≤rank M) :
    (hyperplanes M).biUnion (fun H => H.toFinset.powersetCard (rank M-1)) =
      M.E.toFinset.powersetCard (rank M-1) := by
  ext S
  constructor
  · intro hS
    obtain ⟨H, hH, hSH⟩ := mem_biUnion.mp hS
    obtain ⟨hsub, hc⟩ := mem_powersetCard.mp hSH
    refine mem_powersetCard.mpr ⟨?_, hc⟩
    intro e he
    exact Set.mem_toFinset.mpr (((mem_hyperplanes M H).mp hH).1.subset_ground
      (Set.mem_toFinset.mp (hsub he)))
  · intro hS
    obtain ⟨hSE, hc⟩ := mem_powersetCard.mp hS
    obtain ⟨H, hH, hSH⟩ := hM.exists_hyperplane_superset (S:=(S:Set α))
      (by intro e he; exact Set.mem_toFinset.mp (hSE he))
      (by rw [Set.ncard_coe_finset,hc]; omega)
    exact mem_biUnion.mpr ⟨H, (mem_hyperplanes M H).mpr hH,
      mem_powersetCard.mpr ⟨fun e he => Set.mem_toFinset.mpr (hSH he), hc⟩⟩

/-- The complete actual hyperplane family partitions the (rank−1)-subsets. -/
theorem IsPaving.hyperplane_packing_eq (hM : IsPaving M) (hr : 1≤rank M) :
    (∑ H ∈ hyperplanes M, H.ncard.choose (rank M-1)) = M.E.ncard.choose (rank M-1) := by
  have hd : ((hyperplanes M) : Set (Set α)).PairwiseDisjoint
      (fun H => H.toFinset.powersetCard (rank M-1)) := by
    intro H hH K hK hne
    exact hM.hyperplane_blocks_disjoint hr ((mem_hyperplanes M H).mp hH)
      ((mem_hyperplanes M K).mp hK) hne
  have h := congrArg Finset.card (hM.hyperplane_block_cover hr)
  rw [Finset.card_biUnion hd] at h
  simpa only [card_powersetCard, ← Set.ncard_eq_toFinset_card'] using h

end Paving
