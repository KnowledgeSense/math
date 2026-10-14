import Dowling.MatroidDeletionColoopGeometry
import Fan.ProductInvariants

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
def coloopSplitSet (e : α) (S : Set α) (b : Bool) : Set α := if b then insert e S else S

omit [Fintype α] in
theorem coloopSplitSet_le_iff (e : α) (S T : Set α) (heS : e∉S) (heT : e∉T) (a b : Bool) :
    coloopSplitSet e S a⊆coloopSplitSet e T b ↔ S⊆T ∧ a≤b := by
  have htf : ¬(true≤false) := by decide
  cases a <;> cases b <;> simp only [coloopSplitSet,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_le,Bool.le_true,and_true,htf,and_false,iff_false]
  · constructor
    · intro h x hx
      rcases h hx with hxe | hxt
      · exact False.elim (heS (hxe ▸ hx))
      · exact hxt
    · exact fun h => h.trans (Set.subset_insert _ _)
  · intro h
    exact heT (h (Set.mem_insert _ _))
  · constructor
    · intro h x hx
      rcases h (Or.inr hx) with hxe | hxt
      · exact False.elim (heS (hxe ▸ hx))
      · exact hxt
    · exact Set.insert_subset_insert

instance deletionIicLocallyFiniteOrder (M : Matroid α) (e : α) (F : Flat M) :
    LocallyFiniteOrder (Set.Iic (deletionFlat M e F)) := Fintype.toLocallyFiniteOrder

/-- Literal product decomposition at a local coloop. -/
def coloopLowerEmbedding (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) :
    (Set.Iic (deletionFlat M e F) × Bool) ↪o Flat M where
  toFun p := ⟨coloopSplitSet e p.1.val.val p.2,by
    cases hb : p.2 with
    | false => exact deletion_below_old_flat M e F hF p.1.val p.1.property
    | true => exact insert_flat_below_coloop M e F he hF p.1.val p.1.property⟩
  inj' := by
    intro a b h
    have heq := congrArg Subtype.val h
    have hab := (coloopSplitSet_le_iff e a.1.val.val b.1.val.val
      (deletionFlat_not_mem M e a.1.val) (deletionFlat_not_mem M e b.1.val) a.2 b.2).mp heq.le
    have hba := (coloopSplitSet_le_iff e b.1.val.val a.1.val.val
      (deletionFlat_not_mem M e b.1.val) (deletionFlat_not_mem M e a.1.val) b.2 a.2).mp heq.ge
    exact Prod.ext (Subtype.ext (Subtype.ext (Set.Subset.antisymm hab.1 hba.1)))
      (le_antisymm hab.2 hba.2)
  map_rel_iff' := by
    intro a b
    exact coloopSplitSet_le_iff e a.1.val.val b.1.val.val
      (deletionFlat_not_mem M e a.1.val) (deletionFlat_not_mem M e b.1.val) a.2 b.2

end MatroidInverseZ
