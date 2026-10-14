import Paving.PointedPacking

namespace Paving
attribute [local instance] Classical.propDecidable
open Finset MatroidInverseZ
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem rank_le_ground_card (M : Matroid α) : rank M ≤ M.E.ncard := by
  have h := subsetRank_le_card M M.E
  simpa only [subsetRank, M.eRk_ground, rank] using h

/-- Enumeration of the actual low-rank flats above a specified flat. -/
theorem IsPaving.low_flat_mobius_sum (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) :
    (∑ G ∈ (Ico F ⊤).filter (fun G => G.1.ncard≤d), IncidenceAlgebra.mu ℤ F G) =
      ∑ S ∈ (Icc F.1.toFinset M.E.toFinset).filter (fun S => S.card≤d),
        (-1 : ℤ)^(S.card-F.1.ncard) := by
  classical
  apply sum_bij (fun G _ => G.1.toFinset)
  · intro G hG
    obtain ⟨hG,hcard⟩ := mem_filter.mp hG
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_,?_⟩, ?_⟩
    · exact Set.toFinset_subset_toFinset.mpr (mem_Ico.mp hG).1
    · exact Set.toFinset_subset_toFinset.mpr G.2.subset_ground
    · simpa only [← Set.ncard_eq_toFinset_card'] using hcard
  · intro G _ H _ he
    apply Subtype.ext
    have h := congrArg (fun S : Finset α => (S : Set α)) he
    simpa only [Set.coe_toFinset] using h
  · intro S hS
    obtain ⟨hS,hcard⟩ := mem_filter.mp hS
    have hSE : (S:Set α) ⊆ M.E := by
      intro e he
      exact Set.mem_toFinset.mp ((mem_Icc.mp hS).2 he)
    have hflat := hM.small_set_isFlat hSE (by rw [Set.ncard_coe_finset]; omega)
    refine ⟨⟨(S:Set α),hflat⟩, mem_filter.mpr ⟨mem_Ico.mpr ⟨?_,?_⟩,?_⟩,?_⟩
    · intro e he
      exact (mem_Icc.mp hS).1 (Set.mem_toFinset.mpr he)
    · apply lt_of_le_of_ne le_top
      intro he
      have hv := congrArg (fun G : MatroidInverseZ.Flat M => G.1.ncard) he
      change (S:Set α).ncard = M.E.ncard at hv
      rw [Set.ncard_coe_finset] at hv
      have hg := rank_le_ground_card M
      omega
    · simpa only [Set.ncard_coe_finset] using hcard
    · simp
  · intro G hG
    obtain ⟨hG,hcard⟩ := mem_filter.mp hG
    rw [actual_independentFlat_mu G.1 (hM.indep_of_card_lt G.2.subset_ground (by omega))
      G.2 F (mem_Ico.mp hG).1]
    rw [← Set.ncard_eq_toFinset_card']

theorem IsPaving.low_flat_mobius_sum_closed (hM : IsPaving M) (d : ℕ) (hr : rank M=d+2)
    (F : MatroidInverseZ.Flat M) (hF : F.1.ncard≤d) :
    (∑ G ∈ (Ico F ⊤).filter (fun G => G.1.ncard≤d), IncidenceAlgebra.mu ℤ F G) =
      (-1 : ℤ)^(d-F.1.ncard) * (M.E.ncard-F.1.ncard-1).choose (d-F.1.ncard) := by
  rw [hM.low_flat_mobius_sum d hr F]
  have hg := rank_le_ground_card M
  have h := subset_interval_alternating F.1.toFinset M.E.toFinset
    (Set.toFinset_subset_toFinset.mpr F.2.subset_ground) d
    (by simpa only [← Set.ncard_eq_toFinset_card'] using hF)
    (by simp only [← Set.ncard_eq_toFinset_card']; omega)
  simpa only [← Set.ncard_eq_toFinset_card'] using h

end Paving
