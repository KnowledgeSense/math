import Paving.HighCoefficients
import Paving.HyperplaneIntervals

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The rank-k flats, strictly below hyperplanes, are exactly the k-subsets. -/
theorem IsPaving.sum_rank_flats (hM : IsPaving M) (k : ℕ) (hk : k+1<rank M)
    (w : Set α → ℤ) :
    (∑ F ∈ (univ : Finset (MatroidInverseZ.Flat M)).filter
      (fun F => MatroidInverseZ.flatRank M F=k), w F.1) =
      ∑ S ∈ M.E.toFinset.powersetCard k, w (S:Set α) := by
  apply sum_bij (fun F _ => F.1.toFinset)
  · intro F hF
    have hr := (mem_filter.mp hF).2
    have hi := hM.flat_indep_of_rank F.2 (by change subsetRank M F.1 = k at hr; omega)
    have hc : F.1.ncard=k := by
      have he : MatroidInverseZ.flatRank M F=F.1.ncard := congrArg ENat.toNat hi.eRk_eq_encard
      omega
    exact mem_powersetCard.mpr ⟨Set.toFinset_subset_toFinset.mpr F.2.subset_ground,
      by simpa only [← Set.ncard_eq_toFinset_card'] using hc⟩
  · intro F _ G _ he
    apply Subtype.ext
    have h := congrArg (fun S : Finset α => (S:Set α)) he
    simpa only [Set.coe_toFinset] using h
  · intro S hS
    obtain ⟨hSE,hcard⟩ := mem_powersetCard.mp hS
    have hsub : (S:Set α) ⊆ M.E := fun e he => Set.mem_toFinset.mp (hSE he)
    have hflat := hM.small_set_isFlat hsub (by rw [Set.ncard_coe_finset,hcard]; exact hk)
    refine ⟨⟨(S:Set α),hflat⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · change (M.eRk (S:Set α)).toNat=k
      rw [hM.small_set_rank hsub (by rw [Set.ncard_coe_finset,hcard]; omega), Set.ncard_coe_finset,hcard]
    · simp
  · intro F _
    simp

/-- A fixed hyperplane contains exactly its own k-subsets, counted without multiplicity. -/
theorem subset_hyperplane_sum (H E : Set α) (hHE : H ⊆ E) (k : ℕ) (z : ℤ) :
    (∑ S ∈ E.toFinset.powersetCard k, if (S:Set α) ⊆ H then z else 0) =
      (H.ncard.choose k:ℤ)*z := by
  classical
  rw [← sum_filter]
  have he : (E.toFinset.powersetCard k).filter (fun (S : Finset α) => (S:Set α) ⊆ H) =
      H.toFinset.powersetCard k := by
    ext S
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨_,hc⟩,hSH⟩
      exact ⟨fun e he => Set.mem_toFinset.mpr (hSH he),hc⟩
    · rintro ⟨hSH,hc⟩
      exact ⟨⟨fun e he => Set.mem_toFinset.mpr (hHE (Set.mem_toFinset.mp (hSH he))),hc⟩,
        fun e he => Set.mem_toFinset.mp (hSH he)⟩
  rw [he, sum_const, nsmul_eq_mul, card_powersetCard, ← Set.ncard_eq_toFinset_card']

end Paving
