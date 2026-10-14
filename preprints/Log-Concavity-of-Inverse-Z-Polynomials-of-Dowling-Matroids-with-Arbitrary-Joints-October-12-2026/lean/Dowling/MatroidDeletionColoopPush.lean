import Dowling.MatroidDeletionColoopKL
import Dowling.MatroidDeletionMapOrder
import Dowling.DeletionKLPush

noncomputable section
namespace MatroidInverseZ
open Set Finset LaurentPolynomial Dowling
open scoped Classical
variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem coloopLowerEmbedding_delete (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e}))
    (b : Set.Iic (deletionFlat M e F)) (t : Bool) :
    deletionFlat M e (coloopLowerEmbedding M e F he hF (b,t))=b.val := by
  apply (deletionFlat_fiber_sets M e _ _).mpr
  cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The literal two-flat deletion fiber at a coloop gives the rank-one
Laurent factor, using the actual local KL interval product. -/
theorem coloop_deletionPush (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) (b : Flat (M.delete {e})) :
    deletionPush (flatRank M) (flatRank (M.delete {e})) (deletionFlat M e)
      (deletionKLVector (flatRank M) F) b =
    (T 1+T (-1))*deletionKLVector (flatRank (M.delete {e})) (deletionFlat M e F) b := by
  by_cases hb : b≤deletionFlat M e F
  · let c : Set.Iic (deletionFlat M e F) := ⟨b,hb⟩
    let f := coloopLowerEmbedding M e F he hF
    let a₀ := f (c,false)
    let a₁ := f (c,true)
    have hne : a₀≠a₁ := by
      intro h
      have h' := congrArg Prod.snd (f.injective h)
      exact Bool.noConfusion h'
    have hd (t : Bool) : deletionFlat M e (f (c,t))=b :=
      coloopLowerEmbedding_delete M e F he hF c t
    have hle (t : Bool) : f (c,t)≤F := coloopLowerEmbedding_le M e F he hF _
    have hr (t : Bool) : flatRank M (f (c,t))=flatRank (M.delete {e}) b+coloopBoolRank t :=
      coloopLowerEmbedding_rank M e F he hF _
    have hk (t : Bool) : kl (flatRank M) F (f (c,t))=
        kl (flatRank (M.delete {e})) (deletionFlat M e F) b := by
      rw [coloop_lower_kl M e F he hF _ (hle t),hd t]
    let w : Flat M→DeletionLaurent := fun a =>
      if deletionFlat M e a=b then T ((flatRank (M.delete {e}) b : ℤ)-flatRank M a)*
        deletionKLVector (flatRank M) F a else 0
    have hs : ∑ a,w a = w a₀+w a₁ := by
      have hh : ∑ a∈({a₀,a₁} : Finset (Flat M)),w a=∑ a,w a := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        have hn₀ : a≠a₀ := fun h => ha (by simp [h])
        have hn₁ : a≠a₁ := fun h => ha (by simp [h])
        by_cases hda : deletionFlat M e a=b
        · obtain h | h := (deletionFlat_fiber_sets M e a b).mp hda
          · exact False.elim (hn₀ (Subtype.ext h))
          · exact False.elim (hn₁ (Subtype.ext h))
        · simp [w,hda]
      rw [Finset.sum_pair hne] at hh
      exact hh.symm
    change ∑ a,w a=_
    rw [hs]
    change w (f (c,false))+w (f (c,true))=_
    simp only [w,hd,ite_true,deletionKLVector,hle,hb,hr,hk,coloopBoolRank,
      Bool.false_eq_true,ite_false,Nat.add_zero,Nat.cast_add,Nat.cast_one]
    rw [deletionFlat_rank_drop M e F he hF]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [deletionLift_shift,deletionLift_shift,add_mul,deletionLift_shift,deletionLift_shift]
    congr 2 <;> ring
  · rw [deletionKLVector,ite_eq_right hb,mul_zero]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hd : deletionFlat M e a=b
    · have ha : ¬a≤F := fun h => hb (hd ▸ deletionFlat_monotone M e h)
      simp [hd,deletionKLVector,ha]
    · simp [hd]

end MatroidInverseZ
