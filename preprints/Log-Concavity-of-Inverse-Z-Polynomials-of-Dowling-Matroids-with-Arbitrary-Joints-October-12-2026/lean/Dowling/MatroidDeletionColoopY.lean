import Dowling.MatroidDeletionColoopKL
import Dowling.MatroidDeletionMapOrder
import Dowling.RankOneInvariant

noncomputable section
namespace MatroidInverseZ
open Set Polynomial
open scoped Classical
variable {α : Type*} [Fintype α]

theorem coloopBool_inverseZ : inverseZ coloopBoolRank false true=1+Polynomial.X := by
  have hr : StrictMono coloopBoolRank := by
    intro a b hab
    cases a <;> cases b <;> simp_all [coloopBoolRank]
    exact (show ¬true<false from by decide) hab
  rw [inverseZ_rank_one_split _ hr _ _ (by decide) rfl,
    inverseKL_rank_one _ hr _ _ (by decide) rfl]

/-- A genuine coloop's full flat interval is the deletion interval times a
rank-one chain, hence the ordinary inverse-Z factor is 1+X. -/
theorem matroid_inverseZ_coloop (M : Matroid α) (e : α) (h0 : M.IsFlat ∅)
    (he : e∈M.E) (hf : M.IsFlat (M.E\{e})) :
    matroidInverseZ M=matroidInverseZ (M.delete {e})*(1+Polynomial.X) := by
  let F := topFlat M
  let f := coloopLowerEmbedding M e F he hf
  let x := coloopLowerPreimage M e F (bottomFlat M) (bottomFlat_le M F)
  let y := coloopLowerPreimage M e F F le_rfl
  let r : Set.Iic (deletionFlat M e F)→ℕ := fun b => flatRank (M.delete {e}) b.val
  have hr : Monotone r := by intro b c h; exact deletionFlatRank_monotone M e h
  have h := inverseZ_interval_transport f (coloopLowerEmbedding_interval M e F he hf)
    (fun p => r p.1+coloopBoolRank p.2) (flatRank M)
    (fun u v => congrArg₂ Nat.sub
      (coloopLowerEmbedding_rank M e F he hf v) (coloopLowerEmbedding_rank M e F he hf u)) x y
  have hfx : f x=bottomFlat M := coloopLowerEmbedding_preimage M e F he hf _ _
  have hfy : f y=F := coloopLowerEmbedding_preimage M e F he hf _ _
  rw [hfx,hfy] at h
  have hxy : x≤y := by
    apply f.le_iff_le.mp
    rw [hfx,hfy]
    exact bottomFlat_le M F
  have hx : x.2=false := by simp [x,coloopLowerPreimage,bottomFlat,h0.closure]
  have hy : y.2=true := by simp [y,coloopLowerPreimage,F,topFlat,he]
  change inverseZ (flatRank M) (bottomFlat M) F=_
  rw [h,inverseZ_product r coloopBoolRank hr coloopBoolRank_monotone x y hxy,hx,hy,
    coloopBool_inverseZ]
  congr 1
  let emb : Set.Iic (deletionFlat M e F) ↪o Flat (M.delete {e}) :=
    { toFun := Subtype.val,inj' := Subtype.val_injective,map_rel_iff' := Iff.rfl }
  have ht := inverseZ_interval_transport emb
    (fun _ b z _ hz => ⟨⟨z,hz.trans b.property⟩,rfl⟩)
    r (flatRank (M.delete {e})) (fun _ _ => rfl) x.1 y.1
  change inverseZ (flatRank (M.delete {e})) (deletionFlat M e (bottomFlat M))
    (deletionFlat M e (topFlat M))=_ at ht
  exact ht.symm.trans (congrArg₂ (inverseZ (flatRank (M.delete {e})))
    (deletionFlat_bottom M e) (deletionFlat_top M e))

end MatroidInverseZ
