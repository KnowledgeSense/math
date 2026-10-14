import Dowling.MatroidDeletionColoopProduct

noncomputable section
namespace MatroidInverseZ
open Set
open scoped Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem coloopLowerEmbedding_le (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e}))
    (p : Set.Iic (deletionFlat M e F) × Bool) : coloopLowerEmbedding M e F he hF p≤F := by
  intro x hx
  change x∈coloopSplitSet e p.1.val.val p.2 at hx
  cases hb : p.2 with
  | false => exact (p.1.property (by simpa only [coloopSplitSet,hb,Bool.false_eq_true,ite_false] using hx)).1
  | true =>
    have hx' : x=e ∨ x∈p.1.val.val := by simpa only [coloopSplitSet,hb,ite_true,Set.mem_insert_iff] using hx
    rcases hx' with hxe | hx'
    · exact hxe ▸ he
    · exact (p.1.property hx').1

omit [Fintype α] in
def coloopLowerPreimage (M : Matroid α) (e : α) (F a : Flat M) (ha : a≤F) :
    Set.Iic (deletionFlat M e F) × Bool :=
  (⟨deletionFlat M e a,deletionFlat_monotone M e ha⟩,decide (e∈a.val))

omit [Fintype α] in
theorem coloopLowerEmbedding_preimage (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) (a : Flat M) (ha : a≤F) :
    coloopLowerEmbedding M e F he hF (coloopLowerPreimage M e F a ha)=a := by
  apply Subtype.ext
  change coloopSplitSet e (a.val\{e}) (decide (e∈a.val))=a.val
  by_cases h : e∈a.val
  · simp only [h,decide_true,coloopSplitSet,ite_true,Set.insert_sdiff_singleton,Set.insert_eq_of_mem h]
  · simp only [h,decide_false,coloopSplitSet,Bool.false_eq_true,ite_false,Set.sdiff_singleton_eq_self h]

omit [Fintype α] in
theorem coloopLowerEmbedding_interval (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) :
    ∀ a b y, coloopLowerEmbedding M e F he hF a≤y → y≤coloopLowerEmbedding M e F he hF b →
      ∃ x, coloopLowerEmbedding M e F he hF x=y := by
  intro _ b y _ hy
  have hyF := hy.trans (coloopLowerEmbedding_le M e F he hF b)
  exact ⟨coloopLowerPreimage M e F y hyF,coloopLowerEmbedding_preimage M e F he hF y hyF⟩

def coloopBoolRank (b : Bool) : ℕ := if b then 1 else 0

theorem coloopBoolRank_monotone : Monotone coloopBoolRank := by
  intro a b hab
  cases a <;> cases b <;> simp_all [coloopBoolRank]
  exact (show ¬(true≤false) from by decide) hab

theorem coloopLowerEmbedding_rank (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e}))
    (p : Set.Iic (deletionFlat M e F) × Bool) :
    flatRank M (coloopLowerEmbedding M e F he hF p)=
      flatRank (M.delete {e}) p.1.val+coloopBoolRank p.2 := by
  rcases p with ⟨b,t⟩
  have hbflat := deletion_below_old_flat M e F hF b.val b.property
  have hr : (M.delete {e}).eRk b.val.val=M.eRk b.val.val :=
    M.restrict_eRk_eq b.val.property.subset_ground
  cases t with
  | false =>
    change (M.eRk b.val.val).toNat=((M.delete {e}).eRk b.val.val).toNat+0
    rw [hr,Nat.add_zero]
  | true =>
    have hx : e∈M.E\M.closure b.val.val := by
      rw [hbflat.closure]
      exact ⟨F.property.subset_ground he,deletionFlat_not_mem M e b.val⟩
    have h := congrArg ENat.toNat (M.eRk_insert_eq_add_one hx)
    rw [ENat.toNat_add (finite_eRk_ne_top M _) (by simp)] at h
    change (M.eRk (insert e b.val.val)).toNat=((M.delete {e}).eRk b.val.val).toNat+1
    rw [hr]
    exact h

end MatroidInverseZ
