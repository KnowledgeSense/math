import Paving.FlatRanks

namespace Paving
variable {α : Type*} [Fintype α] {M : Matroid α}

theorem hyperplane_not_subset {H K : Set α} (hH : IsHyperplane M H)
    (hK : IsHyperplane M K) (hne : H ≠ K) : ¬H ⊆ K := by
  intro hsub
  have hr := flat_subsetRank_strict hH.1 hK.1 ⟨hsub, fun h => hne (Set.Subset.antisymm hsub h)⟩
  have h1 := hH.2
  have h2 := hK.2
  omega

/-- The true paving hyperplane intersection bound, including coloops and
all disconnected examples. -/
theorem IsPaving.hyperplane_inter_card {M : Matroid α} (hM : IsPaving M)
    {H K : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hne : H ≠ K) :
    (H ∩ K).ncard + 2 ≤ rank M := by
  have hF : M.IsFlat (H ∩ K) := by
    rw [M.isFlat_iff_closure_eq]
    apply Set.Subset.antisymm _ (M.subset_closure _ (Set.inter_subset_left.trans hH.1.subset_ground))
    apply Set.subset_inter
    · simpa only [hH.1.closure] using M.closure_subset_closure (Set.inter_subset_left : H ∩ K ⊆ H)
    · simpa only [hK.1.closure] using M.closure_subset_closure (Set.inter_subset_right : H ∩ K ⊆ K)
  have hproper : H ∩ K ⊂ H := ⟨Set.inter_subset_left, fun h =>
    hyperplane_not_subset hH hK hne (h.trans Set.inter_subset_right)⟩
  have hlt := flat_subsetRank_strict hF hH.1 hproper
  have hh := hH.2
  have hi := hM.flat_indep_of_rank hF (by omega)
  have hc : subsetRank M (H ∩ K) = (H ∩ K).ncard := congrArg ENat.toNat hi.eRk_eq_encard
  omega

theorem IsPaving.hyperplane_size_coupling {M : Matroid α} (hM : IsPaving M)
    {H K : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hne : H ≠ K) :
    H.ncard + K.ncard + 2 ≤ M.E.ncard + rank M := by
  have hi := hM.hyperplane_inter_card hH hK hne
  have hu := Set.ncard_le_ncard (Set.union_subset hH.1.subset_ground hK.1.subset_ground)
  have he := Set.ncard_union_add_ncard_inter H K
  omega

/-- Distinct large hyperplanes cannot coexist. -/
theorem IsPaving.large_hyperplane_unique {M : Matroid α} (hM : IsPaving M)
    {H K : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hlarge : M.E.ncard + rank M < 2*H.ncard+2) (hsize : H.ncard ≤ K.ncard) : H = K := by
  by_contra hne
  have h := hM.hyperplane_size_coupling hH hK hne
  omega

/-- Every proper flat is either an independent low-rank set or a hyperplane. -/
theorem IsPaving.proper_flat_cases {M : Matroid α} (hM : IsPaving M)
    {F : Set α} (hF : M.IsFlat F) (hne : F ≠ M.E) :
    (M.Indep F ∧ F.ncard+1 < rank M) ∨ IsHyperplane M F := by
  have hlt := flat_subsetRank_strict hF M.ground_isFlat
    ⟨hF.subset_ground, fun h => hne (Set.Subset.antisymm hF.subset_ground h)⟩
  have htop : subsetRank M M.E = rank M := by simp only [subsetRank, rank, M.eRk_ground]
  rw [htop] at hlt
  by_cases hlow : subsetRank M F + 1 < rank M
  · left
    have hi := hM.flat_indep_of_rank hF hlow
    have hc : subsetRank M F = F.ncard := congrArg ENat.toNat hi.eRk_eq_encard
    exact ⟨hi, by omega⟩
  · exact Or.inr ⟨hF, by omega⟩

/-- Every rank-sized subset of a paving hyperplane is genuinely a circuit. -/
theorem IsPaving.hyperplane_subset_isCircuit {M : Matroid α} (hM : IsPaving M)
    {H C : Set α} (hH : IsHyperplane M H) (hCH : C ⊆ H) (hc : C.ncard = rank M) :
    M.IsCircuit C := by
  have hCE := hCH.trans hH.1.subset_ground
  have hdep : M.Dep C := by
    apply (M.not_indep_iff hCE).mp
    intro hi
    have hle := subsetRank_mono M hCH
    have he : subsetRank M C = C.ncard := congrArg ENat.toNat hi.eRk_eq_encard
    have hh := hH.2
    omega
  rw [Matroid.isCircuit_iff]
  refine ⟨hdep, ?_⟩
  intro D hD hDC
  by_contra hne
  have hlt := Set.ncard_lt_ncard (show D ⊂ C from ⟨hDC, fun h => hne (Set.Subset.antisymm hDC h)⟩)
  exact hD.not_indep (hM.indep_of_card_lt (hDC.trans hCE) (by omega))

end Paving
