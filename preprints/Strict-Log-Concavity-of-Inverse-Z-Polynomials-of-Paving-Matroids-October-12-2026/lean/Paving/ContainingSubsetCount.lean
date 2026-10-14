import Paving.SubsetIntervalSums

namespace Paving
open Finset
variable {α : Type*} [DecidableEq α]

theorem containing_subsets_image (A B : Finset α) (hAB : A ⊆ B) (t : ℕ) (hAt : A.card≤t) :
    (B.powersetCard t).filter (fun G => A ⊆ G) =
      ((B \ A).powersetCard (t-A.card)).image (fun S => A ∪ S) := by
  ext G
  constructor
  · intro hG
    obtain ⟨hG, hAG⟩ := mem_filter.mp hG
    obtain ⟨hGB, hc⟩ := mem_powersetCard.mp hG
    refine mem_image.mpr ⟨G \ A, mem_powersetCard.mpr ⟨sdiff_subset_sdiff hGB (subset_refl _), ?_⟩, ?_⟩
    · rw [card_sdiff_of_subset hAG,hc]
    · exact union_sdiff_of_subset hAG
  · intro hG
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hG
    obtain ⟨hSB, hc⟩ := mem_powersetCard.mp hS
    have hd : Disjoint A S := by
      apply disjoint_left.mpr
      intro e he heS
      exact (mem_sdiff.mp (hSB heS)).2 he
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨union_subset hAB (hSB.trans sdiff_subset), ?_⟩, subset_union_left⟩
    rw [card_union_of_disjoint hd,hc]
    omega

theorem containing_subsets_card (A B : Finset α) (hAB : A ⊆ B) (t : ℕ) (hAt : A.card≤t) :
    ((B.powersetCard t).filter (fun G => A ⊆ G)).card = (B.card-A.card).choose (t-A.card) := by
  rw [containing_subsets_image A B hAB t hAt, card_image_iff.mpr, card_powersetCard,
    card_sdiff_of_subset hAB]
  intro S hS T hT he
  have hS' := (mem_powersetCard.mp hS).1
  have hT' := (mem_powersetCard.mp hT).1
  change A ∪ S = A ∪ T at he
  ext e
  constructor
  · intro hes
    have hem : e ∈ A ∪ T := by rw [← he]; exact mem_union_right _ hes
    exact (mem_union.mp hem).resolve_left (mem_sdiff.mp (hS' hes)).2
  · intro het
    have hem : e ∈ A ∪ S := by rw [he]; exact mem_union_right _ het
    exact (mem_union.mp hem).resolve_left (mem_sdiff.mp (hT' het)).2

theorem containing_subsets_card_ite (A B : Finset α) (t : ℕ) (hAt : A.card≤t) :
    ((B.powersetCard t).filter (fun G => A ⊆ G)).card =
      if A ⊆ B then (B.card-A.card).choose (t-A.card) else 0 := by
  by_cases hAB : A ⊆ B
  · rw [ite_eq_left hAB, containing_subsets_card A B hAB t hAt]
  · rw [ite_eq_right hAB, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro G hG
    obtain ⟨hG,hAG⟩ := mem_filter.mp hG
    exact hAB (hAG.trans (mem_powersetCard.mp hG).1)

end Paving
