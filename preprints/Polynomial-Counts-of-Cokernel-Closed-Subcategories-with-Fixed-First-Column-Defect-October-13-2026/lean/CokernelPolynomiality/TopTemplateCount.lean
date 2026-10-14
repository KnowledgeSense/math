import CokernelPolynomiality.ThresholdCompletion
import CokernelPolynomiality.CodeCounting
import Mathlib.Data.Fintype.CardEmbedding

namespace CokernelPolynomiality
noncomputable section
variable {i : ℕ}

 def remainingLevels (e : Fin i ↪ Fin (2*i)) : Finset (Fin (2*i)) := by
  classical
  exact (Finset.univ.image e)ᶜ

 theorem remainingLevels_card (e : Fin i ↪ Fin (2*i)) : (remainingLevels e).card = i := by
  classical
  rw [remainingLevels,Finset.card_compl,Finset.card_image_of_injective _ e.injective]
  simp
  omega

 def placement (e : Fin i ↪ Fin (2*i)) : Fin i ↪o Fin (2*i) :=
  (remainingLevels e).orderEmbOfFin (remainingLevels_card e)

 theorem placement_ne (e : Fin i ↪ Fin (2*i)) (j k : Fin i) : placement e j ≠ e k := by
  classical
  have h := (remainingLevels e).orderEmbOfFin_mem (remainingLevels_card e) j
  change placement e j ∈ (Finset.univ.image e)ᶜ at h
  intro he
  rw [he] at h
  exact (Finset.mem_compl.mp h) (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

 def embeddingCode (e : Fin i ↪ Fin (2*i)) : Code i (2*i) where
  d j := (placement e j).succ
  y j := (e j).succ
  epsilon := completion (fun j => (placement e j).succ) (fun j => (e j).succ)
  monotone_d := fun _ _ h => Fin.succ_le_succ_iff.mpr ((placement e).monotone h)

 theorem embeddingCode_admissible (e : Fin i ↪ Fin (2*i)) : (embeddingCode e).IsAdmissible := by
  apply completion_admissible
  · exact (embeddingCode e).monotone_d
  · intro j k h
    exact placement_ne e k j (Fin.succ_inj.mp h).symm

 theorem embeddingCode_normalized (e : Fin i ↪ Fin (2*i)) : (embeddingCode e).IsNormalized := by
  classical
  intro k hk
  let t := k.pred hk
  have ht : t.succ = k := Fin.succ_pred k hk
  by_cases he : t ∈ Finset.univ.image e
  · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp he
    exact ⟨j,Or.inr (by change (e j).succ = k; rw [hj,ht])⟩
  · have hm : t ∈ remainingLevels e := Finset.mem_compl.mpr he
    let j := ((remainingLevels e).orderIsoOfFin (remainingLevels_card e)).symm ⟨t,hm⟩
    have hj : placement e j = t := by
      exact congrArg Subtype.val (((remainingLevels e).orderIsoOfFin (remainingLevels_card e)).apply_symm_apply ⟨t,hm⟩)
    exact ⟨j,Or.inl (by change (placement e j).succ = k; rw [hj,ht])⟩

 theorem top_y_ne_zero (c : NormalCode i (2*i)) (j : Fin i) : c.val.y j ≠ 0 :=
  (top_coordinates_bijective c.val c.property.2).2 (.inr j)

 theorem top_d_ne_zero (c : NormalCode i (2*i)) (j : Fin i) : c.val.d j ≠ 0 :=
  (top_coordinates_bijective c.val c.property.2).2 (.inl j)

 def topEmbedding (c : NormalCode i (2*i)) : Fin i ↪ Fin (2*i) where
  toFun j := (c.val.y j).pred (top_y_ne_zero c j)
  inj' := by
    intro j k h
    have hh := congrArg Fin.succ h
    simp only [Fin.succ_pred] at hh
    exact Sum.inr.inj ((top_coordinates_bijective c.val c.property.2).1 hh)

 theorem topEmbedding_succ (c : NormalCode i (2*i)) (j : Fin i) :
    (topEmbedding c j).succ = c.val.y j := Fin.succ_pred _ (top_y_ne_zero c j)

 theorem topEmbedding_embeddingCode (e : Fin i ↪ Fin (2*i)) :
    topEmbedding ⟨embeddingCode e,embeddingCode_admissible e,embeddingCode_normalized e⟩ = e := by
  apply Function.Embedding.ext
  intro j
  apply Fin.succ_injective (2*i)
  rw [topEmbedding_succ]
  rfl

 theorem top_placement_recovery (c : NormalCode i (2*i)) (j : Fin i) :
    (placement (topEmbedding c) j).succ = c.val.d j := by
  classical
  have hi := (top_coordinates_bijective c.val c.property.2).1
  have hz : ∀ j, c.val.d j ≠ 0 := top_d_ne_zero c
  have hd : StrictMono c.val.d := by
    intro a b hab
    apply lt_of_le_of_ne (c.val.monotone_d hab.le)
    intro he
    exact (ne_of_lt hab) (Sum.inl.inj (hi he))
  let f : Fin i ↪o Fin (2*i) := OrderEmbedding.ofStrictMono
    (fun j => (c.val.d j).pred (hz j)) (by
      intro a b hab
      have hh := hd hab
      have ha := Fin.succ_pred (c.val.d a) (hz a)
      have hb := Fin.succ_pred (c.val.d b) (hz b)
      rw [← ha,← hb] at hh
      exact Fin.succ_lt_succ_iff.mp hh)
  have hf : f = placement (topEmbedding c) := by
    apply Finset.orderEmbOfFin_unique'
    intro a
    apply Finset.mem_compl.mpr
    intro hm
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hm
    have hh := congrArg Fin.succ hb
    rw [topEmbedding_succ] at hh
    change c.val.y b = ((c.val.d a).pred (hz a)).succ at hh
    rw [Fin.succ_pred] at hh
    have hbad := hi (show c.val.coordinate (.inr b) = c.val.coordinate (.inl a) from hh)
    cases hbad
  rw [← hf]
  exact Fin.succ_pred _ (hz j)

 theorem topEmbedding_injective : Function.Injective (@topEmbedding i) := by
  intro c d h
  apply Subtype.ext
  apply Code.data_injective
  have hy : c.val.y = d.val.y := by
    funext j
    rw [← topEmbedding_succ c j,← topEmbedding_succ d j,h]
  have hd : c.val.d = d.val.d := by
    funext j
    rw [← top_placement_recovery c j,← top_placement_recovery d j,h]
  have hc := (top_template_admissible_iff c.val c.property.2).mp c.property.1
  have hh := (top_template_admissible_iff d.val d.property.2).mp d.property.1
  simp only [hd,hy,hc,hh]

 def topTemplateEquiv (i : ℕ) : NormalCode i (2*i) ≃ (Fin i ↪ Fin (2*i)) :=
  Equiv.ofBijective topEmbedding ⟨topEmbedding_injective,fun e =>
    ⟨⟨embeddingCode e,embeddingCode_admissible e,embeddingCode_normalized e⟩,
      topEmbedding_embeddingCode e⟩⟩

 theorem top_template_count (i : ℕ) : templateCount i (2*i) = (2*i).descFactorial i := by
  classical
  unfold templateCount
  rw [Fintype.card_congr (topTemplateEquiv i),Fintype.card_embedding_eq]
  simp

end
end CokernelPolynomiality
