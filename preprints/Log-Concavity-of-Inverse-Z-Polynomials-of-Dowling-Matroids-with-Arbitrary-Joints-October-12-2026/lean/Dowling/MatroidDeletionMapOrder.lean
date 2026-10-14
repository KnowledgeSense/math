import Dowling.MatroidDeletionMapRank

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

instance deletionFlatOrderBot (M : Matroid α) : OrderBot (Flat M) where
  bot := bottomFlat M
  bot_le F := by
    change M.closure ∅⊆F.val
    exact (M.closure_subset_closure (Set.empty_subset F.val)).trans_eq F.property.closure

instance deletionFlatOrderTop (M : Matroid α) : OrderTop (Flat M) where
  top := topFlat M
  le_top F := F.property.subset_ground

theorem flatRank_monotone (M : Matroid α) : Monotone (flatRank M) := by
  intro F H hFH
  exact ENat.toNat_le_toNat (M.eRk_mono hFH) (finite_eRk_ne_top M _)

/-- Equal finite ranks on comparable actual flats imply equal closures. -/
theorem flatRank_strictMono (M : Matroid α) : StrictMono (flatRank M) := by
  intro F H hFH
  have hle := M.eRk_mono hFH.le
  have hne : M.eRk F.val≠M.eRk H.val := by
    intro he
    have hc := (M.isRkFinite_set F.val).closure_eq_closure_of_subset_of_eRk_ge_eRk hFH.le he.ge
    rw [F.property.closure,H.property.closure] at hc
    exact hFH.ne (Subtype.ext hc)
  have hlt := lt_of_le_of_ne hle hne
  rw [← ENat.natCast_toNat (finite_eRk_ne_top M F.val),
    ← ENat.natCast_toNat (finite_eRk_ne_top M H.val)] at hlt
  exact ENat.natCast_lt_natCast.mp hlt

omit [Fintype α] in
@[simp] theorem flatRank_bottom (M : Matroid α) : flatRank M (bottomFlat M)=0 := by
  change (M.eRk (M.closure ∅)).toNat=0
  simp

omit [Fintype α] in
@[simp] theorem flatRank_top (M : Matroid α) : flatRank M (topFlat M)=M.eRank.toNat := by
  change (M.eRk M.E).toNat=M.eRank.toNat
  rw [← Matroid.eRank_def]

omit [Fintype α] in
theorem bottomFlat_le (M : Matroid α) (F : Flat M) : bottomFlat M≤F := bot_le

omit [Fintype α] in
theorem le_topFlat (M : Matroid α) (F : Flat M) : F≤topFlat M := le_top

theorem flatRank_le_top (M : Matroid α) (F : Flat M) : flatRank M F≤M.eRank.toNat := by
  simpa only [flatRank_top] using flatRank_monotone M (le_topFlat M F)

end MatroidInverseZ
