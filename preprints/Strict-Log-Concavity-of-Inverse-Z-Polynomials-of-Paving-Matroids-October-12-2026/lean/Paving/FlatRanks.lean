import Paving.Definitions

namespace Paving
variable {α : Type*} [Fintype α] {M : Matroid α}

noncomputable def subsetRank (M : Matroid α) (S : Set α) : ℕ := (M.eRk S).toNat

theorem subsetRank_mono (M : Matroid α) {S T : Set α} (h : S ⊆ T) :
    subsetRank M S ≤ subsetRank M T :=
  ENat.toNat_le_toNat (M.eRk_mono h) (M.isRkFinite_set T).eRk_lt_top.ne

theorem flat_subsetRank_strict {F G : Set α} (hF : M.IsFlat F) (hG : M.IsFlat G)
    (hFG : F ⊂ G) : subsetRank M F < subsetRank M G := by
  have hle := M.eRk_mono hFG.subset
  have hne : M.eRk F ≠ M.eRk G := by
    intro he
    have hc := (M.isRkFinite_set F).closure_eq_closure_of_subset_of_eRk_ge_eRk
      hFG.subset he.ge
    rw [hF.closure, hG.closure] at hc
    exact hFG.ne hc
  have hlt := lt_of_le_of_ne hle hne
  rw [← ENat.natCast_toNat (M.isRkFinite_set F).eRk_lt_top.ne,
    ← ENat.natCast_toNat (M.isRkFinite_set G).eRk_lt_top.ne] at hlt
  exact ENat.natCast_lt_natCast.mp hlt

theorem subsetRank_le (M : Matroid α) (S : Set α) : subsetRank M S ≤ rank M :=
  ENat.toNat_le_toNat (M.eRk_le_eRank S) (by simpa only [M.eRk_ground] using (M.isRkFinite_set M.E).eRk_lt_top.ne)

/-- Every low-rank flat of a paving matroid is an independent set, not just
an abstract Boolean interval with the expected rank. -/
theorem IsPaving.flat_indep_of_rank {M : Matroid α} (hM : IsPaving M)
    {F : Set α} (hF : M.IsFlat F) (hr : subsetRank M F + 1 < rank M) : M.Indep F := by
  obtain ⟨I, hI⟩ := M.exists_isBasis F
  have hc : I.ncard = subsetRank M F := congrArg ENat.toNat hI.encard_eq_eRk
  have hiF := hM.small_set_isFlat hI.indep.subset_ground (by omega)
  have he := hI.closure_eq_closure
  rw [hiF.closure, hF.closure] at he
  exact he ▸ hI.indep

/-- Genuine hyperplanes, expressed by their defining flat rank. -/
def IsHyperplane (M : Matroid α) (H : Set α) : Prop :=
  M.IsFlat H ∧ subsetRank M H + 1 = rank M

omit [Fintype α] in
theorem hyperplane_ne_ground {H : Set α} (hH : IsHyperplane M H) : H ≠ M.E := by
  intro he
  have hr := hH.2
  rw [he] at hr
  simp only [subsetRank, M.eRk_ground] at hr
  change rank M + 1 = rank M at hr
  omega

theorem hyperplane_card_lt {H : Set α} (hH : IsHyperplane M H) : H.ncard < M.E.ncard :=
  Set.ncard_lt_ncard ⟨hH.1.subset_ground, fun h => hyperplane_ne_ground hH (Set.Subset.antisymm hH.1.subset_ground h)⟩

end Paving
