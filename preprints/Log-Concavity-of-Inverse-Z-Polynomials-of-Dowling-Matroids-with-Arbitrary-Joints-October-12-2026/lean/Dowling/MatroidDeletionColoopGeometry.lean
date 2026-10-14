import Dowling.MatroidDeletionMapFibers

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*}

/-- Below a flat whose deletion is itself a flat, every deletion flat is
already a flat of the original matroid. -/
theorem deletion_below_old_flat (M : Matroid α) (e : α) (F : Flat M)
    (hF : M.IsFlat (F.val\{e})) (b : Flat (M.delete {e})) (hb : b≤deletionFlat M e F) :
    M.IsFlat b.val := by
  have hc : M.closure b.val⊆F.val\{e} := (M.closure_subset_closure hb).trans_eq hF.closure
  have hd : M.closure b.val\{e}=b.val := congrArg Subtype.val (deletionFlat_closureFlat M e b)
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · intro x hx
    rw [← hd]
    exact ⟨hx,(hc hx).2⟩
  · exact M.subset_closure _ (deletionFlat_subset_ground M e b)

/-- Closure exchange prevents a new point of the old flat from entering after
the independent coloop is inserted. -/
theorem insert_flat_below_coloop (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) (b : Flat (M.delete {e}))
    (hb : b≤deletionFlat M e F) : M.IsFlat (insert e b.val) := by
  have hbflat := deletion_below_old_flat M e F hF b hb
  have hsub : insert e b.val⊆F.val := by
    intro x hx
    rcases hx with hxe | hx
    · exact hxe ▸ he
    · exact (hb hx).1
  have hc : M.closure (insert e b.val)⊆F.val := (M.closure_subset_closure hsub).trans_eq F.property.closure
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxe : x=e
    · exact Or.inl hxe
    · right
      by_contra hxb
      have hxn : x∉M.closure b.val := by rwa [hbflat.closure]
      have hei := Matroid.mem_closure_insert hxn hx
      have hia : insert x b.val⊆F.val\{e} := by
        intro y hy
        rcases hy with hyx | hy
        · exact hyx ▸ ⟨hc hx,hxe⟩
        · exact hb hy
      have hca := (M.closure_subset_closure hia).trans_eq hF.closure
      exact (hca hei).2 (Set.mem_singleton e)
  · exact M.subset_closure _ (hsub.trans F.property.subset_ground)

/-- Every lower old flat remains flat after subtracting the local coloop. -/
theorem lower_flat_remove_coloop (M : Matroid α) (e : α) (F a : Flat M)
    (hF : M.IsFlat (F.val\{e})) (ha : a≤F) : M.IsFlat (a.val\{e}) := by
  have hc : M.closure (a.val\{e})⊆a.val :=
    (M.closure_subset_closure Set.sdiff_subset).trans_eq a.property.closure
  have hd : M.closure (a.val\{e})⊆F.val\{e} :=
    (M.closure_subset_closure (Set.sdiff_subset_sdiff_left ha)).trans_eq hF.closure
  apply Matroid.isFlat_iff_closure_eq.mpr
  exact Set.Subset.antisymm (fun x hx => ⟨hc hx,(hd hx).2⟩)
    (M.subset_closure _ (Set.sdiff_subset.trans a.property.subset_ground))

end MatroidInverseZ
