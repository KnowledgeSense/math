import Dowling.MatroidDeletionColoopIntervals

noncomputable section
namespace MatroidInverseZ
open Set Polynomial Finset
open scoped Classical
variable {α : Type*} [Fintype α]

instance coloopBoolLocallyFiniteOrder : LocallyFiniteOrder Bool := Fintype.toLocallyFiniteOrder

theorem coloopBool_kl (b : Bool) : kl coloopBoolRank true b=1 := by
  cases b with
  | true => exact kl_self _ _
  | false =>
    have hco : Finset.Ico false true={false} := by ext b; cases b <;> simp
    have hoc : Finset.Ioc false true={true} := by ext b; cases b <;> simp
    have hcc : Finset.Icc false true={false,true} := by ext b; cases b <;> simp
    have hm : IncidenceAlgebra.mu ℤ false true=-1 := by
      rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (by decide),hco,sum_singleton,IncidenceAlgebra.mu_self]
    have hc : characteristic coloopBoolRank false true=Polynomial.X-1 := by
      simp [characteristic,hcc,hm,coloopBoolRank,sub_eq_add_neg]
    rw [kl_recurrence,ite_eq_right (by decide),hoc,sum_singleton,kl_self,mul_one,hc]
    simp [coloopBoolRank,belowHalf]

theorem deletionFlatRank_monotone (M : Matroid α) (e : α) :
    Monotone (flatRank (M.delete {e})) := by
  intro a b hab
  exact ENat.toNat_le_toNat ((M.delete {e}).eRk_mono hab) (finite_eRk_ne_top _ _)

/-- The local coloop product gives the exact KL restriction/contraction
identity used by the deletion intertwiner. -/
theorem coloop_lower_kl (M : Matroid α) (e : α) (F : Flat M)
    (he : e∈F.val) (hF : M.IsFlat (F.val\{e})) (a : Flat M) (ha : a≤F) :
    kl (flatRank M) F a=kl (flatRank (M.delete {e})) (deletionFlat M e F) (deletionFlat M e a) := by
  let f := coloopLowerEmbedding M e F he hF
  let x := coloopLowerPreimage M e F a ha
  let y := coloopLowerPreimage M e F F le_rfl
  let r : Set.Iic (deletionFlat M e F) → ℕ := fun b => flatRank (M.delete {e}) b.val
  have hr : Monotone r := by intro b c h; exact deletionFlatRank_monotone M e h
  have h := kl_interval_transport f (coloopLowerEmbedding_interval M e F he hF)
    (fun p => r p.1+coloopBoolRank p.2) (flatRank M)
    (fun u v => by rw [coloopLowerEmbedding_rank,coloopLowerEmbedding_rank]) x y
  rw [coloopLowerEmbedding_preimage,coloopLowerEmbedding_preimage] at h
  have hxy : x≤y := by
    apply f.le_iff_le.mp
    rw [coloopLowerEmbedding_preimage,coloopLowerEmbedding_preimage]
    exact ha
  rw [h,kl_product r coloopBoolRank hr coloopBoolRank_monotone x y hxy]
  have hy : y.2=true := by simp [y,coloopLowerPreimage,he]
  rw [hy,coloopBool_kl,mul_one]
  let emb : Set.Iic (deletionFlat M e F) ↪o Flat (M.delete {e}) :=
    { toFun := Subtype.val,inj' := Subtype.val_injective,map_rel_iff' := Iff.rfl }
  have ht := kl_interval_transport emb
    (fun _ b z _ hz => ⟨⟨z,hz.trans b.property⟩,rfl⟩)
    r (flatRank (M.delete {e})) (fun _ _ => rfl) x.1 y.1
  exact ht.symm

end MatroidInverseZ
