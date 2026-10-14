import Paving.Hyperplanes
import Mathlib.Data.Finset.Powerset

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset
variable {α : Type*} [Fintype α] {M : Matroid α}

noncomputable def hyperplanes (M : Matroid α) : Finset (Set α) :=
  Finset.univ.filter (IsHyperplane M)

noncomputable def stressedHyperplanes (M : Matroid α) : Finset (Set α) :=
  (hyperplanes M).filter (fun H => rank M ≤ H.ncard)

@[simp] theorem mem_hyperplanes (M : Matroid α) (H : Set α) :
    H ∈ hyperplanes M ↔ IsHyperplane M H := by
  classical
  simp [hyperplanes]

@[simp] theorem mem_stressedHyperplanes (M : Matroid α) (H : Set α) :
    H ∈ stressedHyperplanes M ↔ IsHyperplane M H ∧ rank M ≤ H.ncard := by
  classical
  simp [stressedHyperplanes]

/-- Actual hyperplane blocks of independent (rank−1)-subsets are disjoint. -/
theorem IsPaving.hyperplane_blocks_disjoint (hM : IsPaving M) (hr : 1 ≤ rank M)
    {H K : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hne : H ≠ K) :
    Disjoint (H.toFinset.powersetCard (rank M-1))
      (K.toFinset.powersetCard (rank M-1)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro I hiH hiK
  obtain ⟨hiH, hi⟩ := Finset.mem_powersetCard.mp hiH
  obtain ⟨hiK, _⟩ := Finset.mem_powersetCard.mp hiK
  have hsub : (I : Set α) ⊆ H ∩ K := by
    intro e he
    exact ⟨Set.mem_toFinset.mp (hiH he), Set.mem_toFinset.mp (hiK he)⟩
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hi] at hc
  have hbound := hM.hyperplane_inter_card hH hK hne
  omega

/-- The packing constraint follows from the actual finite hyperplane system. -/
theorem IsPaving.hyperplane_packing (hM : IsPaving M) (hr : 1 ≤ rank M)
    (A : Finset (Set α)) (hA : ∀ H∈A, IsHyperplane M H) :
    (∑ H ∈ A, H.ncard.choose (rank M-1)) ≤ M.E.ncard.choose (rank M-1) := by
  classical
  let B := fun H : Set α => H.toFinset.powersetCard (rank M-1)
  have hd : (A : Set (Set α)).PairwiseDisjoint B := by
    intro H hH K hK hne
    exact hM.hyperplane_blocks_disjoint hr (hA H hH) (hA K hK) hne
  have hs : A.biUnion B ⊆ M.E.toFinset.powersetCard (rank M-1) := by
    intro I hI
    obtain ⟨H, hH, hIH⟩ := Finset.mem_biUnion.mp hI
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hIH
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hc⟩
    intro e he
    exact Set.mem_toFinset.mpr ((hA H hH).1.subset_ground (Set.mem_toFinset.mp (hsub he)))
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hd] at hc
  simpa only [B, Finset.card_powersetCard, ← Set.ncard_eq_toFinset_card'] using hc

theorem IsPaving.stressedHyperplane_packing (hM : IsPaving M) (hr : 1 ≤ rank M) :
    (∑ H ∈ stressedHyperplanes M, H.ncard.choose (rank M-1)) ≤
      M.E.ncard.choose (rank M-1) :=
  hM.hyperplane_packing hr _ (fun H hH => (mem_stressedHyperplanes M H).mp hH |>.1)

end Paving
