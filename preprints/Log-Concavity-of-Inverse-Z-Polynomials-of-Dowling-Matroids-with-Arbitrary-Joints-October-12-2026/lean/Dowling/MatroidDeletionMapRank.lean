import Dowling.MatroidDeletionMap

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

theorem finite_eRk_ne_top (M : Matroid α) (S : Set α) : M.eRk S≠⊤ :=
  (M.isRkFinite_of_finite S.toFinite).eRk_lt_top.ne

omit [Fintype α] in
theorem closureFlat_rank (M : Matroid α) (e : α) (b : Flat (M.delete {e})) :
    flatRank M (closureFlat M e b)=flatRank (M.delete {e}) b := by
  unfold flatRank closureFlat
  rw [Matroid.eRk_closure_eq]
  exact congrArg ENat.toNat (M.restrict_eRk_eq b.property.subset_ground).symm

omit [Fintype α] in
theorem deletionFlat_eRk (M : Matroid α) (e : α) (a : Flat M) :
    (M.delete {e}).eRk (deletionFlat M e a).val=M.eRk (a.val\{e}) := by
  exact M.restrict_eRk_eq (Set.sdiff_subset_sdiff_left a.property.subset_ground)

theorem deletionFlat_rank_le (M : Matroid α) (e : α) (a : Flat M) :
    flatRank (M.delete {e}) (deletionFlat M e a)≤flatRank M a := by
  unfold flatRank
  rw [deletionFlat_eRk]
  exact ENat.toNat_le_toNat (M.eRk_mono Set.sdiff_subset) (finite_eRk_ne_top M _)

theorem rank_le_deletionFlat_rank_add_one (M : Matroid α) (e : α) (a : Flat M) :
    flatRank M a≤flatRank (M.delete {e}) (deletionFlat M e a)+1 := by
  have hs : a.val⊆insert e (a.val\{e}) := by
    intro x hx
    by_cases he : x=e
    · exact Or.inl he
    · exact Or.inr ⟨hx,he⟩
  have h := (M.eRk_mono hs).trans (M.eRk_insert_le_add_one e (a.val\{e}))
  have ht := ENat.toNat_le_toNat h (by
    simp [finite_eRk_ne_top M _])
  rw [ENat.toNat_add (finite_eRk_ne_top M _) (by simp)] at ht
  change (M.eRk a.val).toNat≤(M.eRk (a.val\{e})).toNat+1 at ht
  unfold flatRank
  rw [deletionFlat_eRk]
  exact ht

omit [Fintype α] in
theorem deletion_spanning_of_not_coloop (M : Matroid α) (e : α) (he : ¬M.IsColoop e) :
    M.Spanning (M.E\{e}) := by
  by_contra h
  exact he (Matroid.isColoop_iff_sdiff_not_spanning.mpr h)

omit [Fintype α] in
theorem closureFlat_top_of_not_coloop (M : Matroid α) (e : α) (he : ¬M.IsColoop e) :
    closureFlat M e (topFlat (M.delete {e}))=topFlat M := by
  apply Subtype.ext
  exact (deletion_spanning_of_not_coloop M e he).closure_eq

omit [Fintype α] in
theorem deletion_eRank_of_not_coloop (M : Matroid α) (e : α) (he : ¬M.IsColoop e) :
    (M.delete {e}).eRank=M.eRank :=
  (deletion_spanning_of_not_coloop M e he).eRank_restrict

omit [Fintype α] in
theorem deletion_top_rank_of_not_coloop (M : Matroid α) (e : α) (he : ¬M.IsColoop e) :
    flatRank (M.delete {e}) (topFlat (M.delete {e}))=flatRank M (topFlat M) := by
  change ((M.delete {e}).eRk (M.delete {e}).E).toNat=(M.eRk M.E).toNat
  rw [← Matroid.eRank_def,← Matroid.eRank_def,deletion_eRank_of_not_coloop M e he]

end MatroidInverseZ
