import Paving.TruncatedEvaluation

namespace Paving
open Finset
variable {α : Type*} [DecidableEq α]

theorem subset_interval_sum_card (A B : Finset α) (hAB : A ⊆ B) (w : ℕ → ℤ) :
    (∑ G ∈ Icc A B, w (G.card-A.card)) =
      ∑ k ∈ range (B.card-A.card+1), ((B.card-A.card).choose k:ℤ)*w k := by
  rw [Finset.Icc_eq_image_powerset hAB, sum_image]
  · have hsum : (∑ S ∈ (B \ A).powerset, w ((A ∪ S).card-A.card)) =
        ∑ S ∈ (B \ A).powerset, w S.card := by
      apply sum_congr rfl
      intro S hS
      have hd : Disjoint A S := by
        apply disjoint_left.mpr
        intro e he heS
        exact (mem_sdiff.mp ((mem_powerset.mp hS) heS)).2 he
      rw [card_union_of_disjoint hd, Nat.add_sub_cancel_left]
    rw [hsum, Finset.sum_powerset]
    simp only [Finset.sum_powersetCard, nsmul_eq_mul, card_sdiff_of_subset hAB]
  · intro S hS T hT he
    change A ∪ S = A ∪ T at he
    have hS' := mem_powerset.mp hS
    have hT' := mem_powerset.mp hT
    ext e
    constructor
    · intro hes
      have hem : e ∈ A ∪ T := by rw [← he]; exact mem_union_right _ hes
      exact (mem_union.mp hem).resolve_left (mem_sdiff.mp (hS' hes)).2
    · intro het
      have hem : e ∈ A ∪ S := by rw [he]; exact mem_union_right _ het
      exact (mem_union.mp hem).resolve_left (mem_sdiff.mp (hT' het)).2

/-- The truncated signed Boolean sum above a specified subset. -/
theorem subset_interval_alternating (A B : Finset α) (hAB : A ⊆ B) (d : ℕ)
    (hA : A.card ≤ d) (hB : d < B.card) :
    (∑ G ∈ (Icc A B).filter (fun G => G.card ≤ d), (-1 : ℤ)^(G.card-A.card)) =
      (-1 : ℤ)^(d-A.card) * (B.card-A.card-1).choose (d-A.card) := by
  rw [sum_filter]
  have he : (∑ G ∈ Icc A B, if G.card ≤ d then (-1 : ℤ)^(G.card-A.card) else 0) =
      ∑ G ∈ Icc A B, if G.card-A.card ≤ d-A.card then (-1 : ℤ)^(G.card-A.card) else 0 := by
    apply sum_congr rfl
    intro G hG
    have hc := card_le_card (mem_Icc.mp hG).1
    simp only [show (G.card ≤ d) ↔ (G.card-A.card ≤ d-A.card) by omega]
  rw [he, subset_interval_sum_card A B hAB (fun k => if k≤d-A.card then (-1:ℤ)^k else 0)]
  simp_rw [mul_ite, mul_zero]
  have hs : (∑ k ∈ range (B.card-A.card+1),
      if k ≤ d-A.card then ((B.card-A.card).choose k:ℤ)*(-1:ℤ)^k else 0) =
      ∑ k ∈ range (d-A.card+1), ((B.card-A.card).choose k:ℤ)*(-1:ℤ)^k := by
    apply (sum_subset (by intro k hk; exact mem_range.mpr (by have := mem_range.mp hk; omega)) ?_).symm.trans
      (sum_congr rfl (fun k hk => by rw [ite_eq_left (by have := mem_range.mp hk; omega)]))
    intro k _ hk
    exact ite_eq_right (by simpa only [mem_range, Nat.lt_succ_iff] using hk)
  rw [hs]
  have hc : B.card-A.card=(B.card-A.card-1)+1 := by omega
  simp_rw [mul_comm (((B.card-A.card).choose _):ℤ)]
  rw [hc, Int.alternating_sum_range_choose_eq_choose]
  simp only [Nat.add_sub_cancel]

end Paving
