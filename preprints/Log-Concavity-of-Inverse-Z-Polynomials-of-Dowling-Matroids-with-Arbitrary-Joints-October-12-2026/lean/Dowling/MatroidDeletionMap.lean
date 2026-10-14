import ThagomizerTuran.MatroidDefinitions
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Combinatorics.Matroid.Rank.ENat

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*}

/-- Literal deletion of an element from an actual flat. -/
def deletionFlat (M : Matroid α) (e : α) (F : Flat M) : Flat (M.delete {e}) :=
  ⟨F.val\{e},by
    apply Matroid.isFlat_iff_closure_eq.mpr
    rw [Matroid.delete_closure_eq,sdiff_sdiff_left,sup_idem]
    apply Set.Subset.antisymm
    · exact Set.sdiff_subset_sdiff_left ((M.closure_subset_closure Set.sdiff_subset).trans_eq F.property.closure)
    · intro x hx
      exact ⟨M.subset_closure _ (Set.sdiff_subset.trans F.property.subset_ground) hx,hx.2⟩⟩

/-- Closure in the original matroid is the canonical lift of a deletion flat. -/
def closureFlat (M : Matroid α) (e : α) (F : Flat (M.delete {e})) : Flat M :=
  ⟨M.closure F.val,M.isFlat_closure _⟩

theorem deletionFlat_monotone (M : Matroid α) (e : α) : Monotone (deletionFlat M e) :=
  fun _ _ h => Set.sdiff_subset_sdiff_left h

theorem closureFlat_monotone (M : Matroid α) (e : α) : Monotone (closureFlat M e) :=
  fun _ _ h => M.closure_subset_closure h

theorem deletionFlat_not_mem (M : Matroid α) (e : α) (F : Flat (M.delete {e})) : e∉F.val := by
  intro he
  exact (F.property.subset_ground he).2 (Set.mem_singleton e)

theorem deletionFlat_subset_ground (M : Matroid α) (e : α) (F : Flat (M.delete {e})) : F.val⊆M.E :=
  F.property.subset_ground.trans Set.sdiff_subset

theorem deletionFlat_closureFlat (M : Matroid α) (e : α) (F : Flat (M.delete {e})) :
    deletionFlat M e (closureFlat M e F)=F := by
  apply Subtype.ext
  change M.closure F.val\{e}=F.val
  rw [← Matroid.delete_closure_eq_of_disjoint M
    (Set.disjoint_singleton_right.mpr (deletionFlat_not_mem M e F))]
  exact F.property.closure

/-- The exact deletion/closure adjunction on the genuine flat posets. -/
theorem closureFlat_le_iff (M : Matroid α) (e : α) (a : Flat M) (b : Flat (M.delete {e})) :
    closureFlat M e b≤a ↔ b≤deletionFlat M e a := by
  constructor
  · intro h x hx
    refine ⟨h (M.subset_closure b.val (deletionFlat_subset_ground M e b) hx),?_⟩
    intro hxe
    have he : x=e := Set.mem_singleton_iff.mp hxe
    exact deletionFlat_not_mem M e b (he ▸ hx)
  · intro h
    change M.closure b.val⊆a.val
    have hba : b.val⊆a.val := fun x hx => (h hx).1
    exact (M.closure_subset_closure hba).trans_eq a.property.closure

theorem deletionFlat_surjective (M : Matroid α) (e : α) : Function.Surjective (deletionFlat M e) :=
  fun F => ⟨closureFlat M e F,deletionFlat_closureFlat M e F⟩

theorem closureFlat_injective (M : Matroid α) (e : α) : Function.Injective (closureFlat M e) := by
  intro a b h
  have he := congrArg (deletionFlat M e) h
  simpa only [deletionFlat_closureFlat] using he

theorem deletionFlat_top (M : Matroid α) (e : α) :
    deletionFlat M e (topFlat M)=topFlat (M.delete {e}) := rfl

theorem deletionFlat_bottom (M : Matroid α) (e : α) :
    deletionFlat M e (bottomFlat M)=bottomFlat (M.delete {e}) := by
  apply Subtype.ext
  change M.closure ∅\{e}=(M.delete {e}).closure ∅
  rw [Matroid.delete_closure_eq,empty_sdiff]

end MatroidInverseZ
