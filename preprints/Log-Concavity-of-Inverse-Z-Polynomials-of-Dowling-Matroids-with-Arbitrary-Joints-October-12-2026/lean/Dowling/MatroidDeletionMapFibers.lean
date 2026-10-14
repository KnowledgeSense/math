import Dowling.MatroidDeletionMapRank

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem deletionFlat_fiber_sets (M : Matroid α) (e : α) (a : Flat M)
    (b : Flat (M.delete {e})) :
    deletionFlat M e a=b ↔ a.val=b.val ∨ a.val=insert e b.val := by
  constructor
  · intro h
    have hd : a.val\{e}=b.val := congrArg Subtype.val h
    by_cases he : e∈a.val
    · right
      rw [← hd]
      rw [Set.insert_sdiff_singleton,Set.insert_eq_of_mem he]
    · left
      rw [← hd]
      exact (Set.sdiff_singleton_eq_self he).symm
  · intro h
    apply Subtype.ext
    change a.val\{e}=b.val
    rcases h with h | h
    · rw [h,Set.sdiff_singleton_eq_self (deletionFlat_not_mem M e b)]
    · rw [h]
      ext x
      simp only [Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
      have hb := deletionFlat_not_mem M e b
      aesop

omit [Fintype α] in
theorem deletionFlat_rank_eq_of_not_mem (M : Matroid α) (e : α) (a : Flat M)
    (he : e∉a.val) : flatRank (M.delete {e}) (deletionFlat M e a)=flatRank M a := by
  unfold flatRank
  rw [deletionFlat_eRk,Set.sdiff_singleton_eq_self he]

theorem deletionFlat_rank_drop (M : Matroid α) (e : α) (a : Flat M)
    (he : e∈a.val) (hf : M.IsFlat (a.val\{e})) :
    flatRank M a=flatRank (M.delete {e}) (deletionFlat M e a)+1 := by
  have hx : e∈M.E\M.closure (a.val\{e}) := by
    refine ⟨a.property.subset_ground he,?_⟩
    rw [hf.closure]
    exact fun h => h.2 (Set.mem_singleton e)
  have hr := M.eRk_insert_eq_add_one hx
  rw [Set.insert_sdiff_singleton,Set.insert_eq_of_mem he] at hr
  have ht := congrArg ENat.toNat hr
  rw [ENat.toNat_add (finite_eRk_ne_top M _) (by simp)] at ht
  unfold flatRank
  rw [deletionFlat_eRk]
  exact ht

omit [Fintype α] in
/-- The nonflat-removal case has no rank loss, proved using actual closure. -/
theorem deletionFlat_rank_eq_of_not_flat (M : Matroid α) (e : α) (a : Flat M)
    (hf : ¬M.IsFlat (a.val\{e})) : flatRank (M.delete {e}) (deletionFlat M e a)=flatRank M a := by
  have hsub : M.closure (a.val\{e})⊆a.val :=
    (M.closure_subset_closure Set.sdiff_subset).trans_eq a.property.closure
  have he : e∈M.closure (a.val\{e}) := by
    by_contra h
    apply hf
    apply Matroid.isFlat_iff_closure_eq.mpr
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨hsub hx,fun hxe => h (Set.mem_singleton_iff.mp hxe ▸ hx)⟩
    · exact M.subset_closure _ (Set.sdiff_subset.trans a.property.subset_ground)
  have hcl : M.closure (a.val\{e})=a.val := by
    apply Set.Subset.antisymm hsub
    intro x hx
    by_cases hxe : x=e
    · exact hxe ▸ he
    · exact M.subset_closure _ (Set.sdiff_subset.trans a.property.subset_ground) ⟨hx,hxe⟩
  unfold flatRank
  rw [deletionFlat_eRk,← Matroid.eRk_closure_eq M (a.val\{e}),hcl]

end MatroidInverseZ
