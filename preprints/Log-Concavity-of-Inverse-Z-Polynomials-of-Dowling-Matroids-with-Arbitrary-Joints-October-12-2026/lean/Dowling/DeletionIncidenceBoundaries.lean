import Dowling.MatroidDeletionMapOrder
import Dowling.MatroidDeletionMapFibers

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

/-- The actual singleton flat used in the deletion theorem. -/
def deletionSingletonFlat (M : Matroid α) (e : α) (he : M.IsFlat {e}) : Flat M := ⟨{e},he⟩

omit [Fintype α] in
theorem deletion_bottom_val (M : Matroid α) (h0 : M.IsFlat ∅) : (bottomFlat M).val=∅ := h0.closure

omit [Fintype α] in
theorem deletion_delete_bottom_val (M : Matroid α) (e : α) (h0 : M.IsFlat ∅) :
    (bottomFlat (M.delete {e})).val=∅ := by
  change (M.delete {e}).closure ∅=∅
  rw [Matroid.delete_closure_eq,empty_sdiff,h0.closure,empty_sdiff]

omit [Fintype α] in
theorem deletion_bottom_fiber (M : Matroid α) (e : α) (h0 : M.IsFlat ∅)
    (he : M.IsFlat {e}) (F : Flat M) :
    deletionFlat M e F=bottomFlat (M.delete {e})↔
      F=bottomFlat M∨F=deletionSingletonFlat M e he := by
  rw [deletionFlat_fiber_sets,deletion_delete_bottom_val M e h0]
  simp only [insert_empty_eq]
  constructor
  · intro h
    rcases h with h | h
    · left
      apply Subtype.ext
      exact h.trans (deletion_bottom_val M h0).symm
    · right
      exact Subtype.ext h
  · rintro (rfl | rfl)
    · exact Or.inl (deletion_bottom_val M h0)
    · exact Or.inr rfl

 theorem deletionSingletonFlat_rank (M : Matroid α) (e : α) (h0 : M.IsFlat ∅)
    (he : M.IsFlat {e}) : flatRank M (deletionSingletonFlat M e he)=1 := by
  have hd : deletionFlat M e (deletionSingletonFlat M e he)=bottomFlat (M.delete {e}) :=
    (deletion_bottom_fiber M e h0 he _).mpr (Or.inr rfl)
  have h := deletionFlat_rank_drop M e (deletionSingletonFlat M e he) (Set.mem_singleton e)
    (by simpa only [deletionSingletonFlat,sdiff_self] using h0)
  rw [hd,flatRank_bottom,zero_add] at h
  exact h

omit [Fintype α] in
theorem deletionSingletonFlat_le_iff (M : Matroid α) (e : α) (he : M.IsFlat {e}) (F : Flat M) :
    deletionSingletonFlat M e he≤F↔e∈F.val := Set.singleton_subset_iff

end MatroidInverseZ
