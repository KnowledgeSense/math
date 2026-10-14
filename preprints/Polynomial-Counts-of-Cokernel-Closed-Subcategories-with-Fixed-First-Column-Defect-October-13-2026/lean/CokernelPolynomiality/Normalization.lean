import CokernelPolynomiality.FiniteRecoding
import Mathlib.Data.Finset.Sort

namespace CokernelPolynomiality
noncomputable section

variable {i m : ℕ}

 def Code.levelSet (c : Code i m) : Finset (Fin (m+1)) :=
  insert 0 (Finset.univ.image c.d ∪ Finset.univ.image c.y)

 def Code.levelCount (c : Code i m) : ℕ := c.levelSet.card-1

 theorem Code.zero_mem_levelSet (c : Code i m) : (0 : Fin (m+1)) ∈ c.levelSet :=
  Finset.mem_insert_self _ _

 theorem Code.card_levelSet (c : Code i m) : c.levelSet.card = c.levelCount+1 := by
  have hp : 0 < c.levelSet.card := Finset.card_pos.mpr ⟨0,c.zero_mem_levelSet⟩
  unfold Code.levelCount
  omega

 def Code.levelIso (c : Code i m) : Fin (c.levelCount+1) ≃o c.levelSet :=
  c.levelSet.orderIsoOfFin c.card_levelSet

 def Code.levelEmbedding (c : Code i m) : Fin (c.levelCount+1) ↪o Fin (m+1) :=
  c.levelIso.toOrderEmbedding.trans (OrderEmbedding.subtype _)

 theorem Code.levelEmbedding_zero (c : Code i m) : c.levelEmbedding 0 = 0 := by
  let z : c.levelSet := ⟨0,c.zero_mem_levelSet⟩
  have hh := c.levelEmbedding.monotone (Fin.zero_le (c.levelIso.symm z))
  have hz : c.levelEmbedding (c.levelIso.symm z) = 0 := by
    change (c.levelIso (c.levelIso.symm z)).val = 0
    rw [c.levelIso.apply_symm_apply]
  rw [hz] at hh
  exact le_antisymm hh (Fin.zero_le _)

 theorem Code.d_mem_levelSet (c : Code i m) (j : Fin i) : c.d j ∈ c.levelSet := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

 theorem Code.y_mem_levelSet (c : Code i m) (j : Fin i) : c.y j ∈ c.levelSet := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

 def Code.normalize (c : Code i m) : Code i c.levelCount where
  d j := c.levelIso.symm ⟨c.d j,c.d_mem_levelSet j⟩
  y j := c.levelIso.symm ⟨c.y j,c.y_mem_levelSet j⟩
  epsilon := c.epsilon
  monotone_d := by
    intro j k hjk
    apply c.levelIso.symm.monotone
    exact c.monotone_d hjk

 theorem Code.recover_d (c : Code i m) (j : Fin i) :
    c.levelEmbedding (c.normalize.d j) = c.d j := by
  change (c.levelIso (c.levelIso.symm ⟨c.d j,c.d_mem_levelSet j⟩)).val = c.d j
  simp

 theorem Code.recover_y (c : Code i m) (j : Fin i) :
    c.levelEmbedding (c.normalize.y j) = c.y j := by
  change (c.levelIso (c.levelIso.symm ⟨c.y j,c.y_mem_levelSet j⟩)).val = c.y j
  simp

 theorem Code.normalize_isNormalized (c : Code i m) : c.normalize.IsNormalized := by
  intro k hk
  have hzero : c.levelEmbedding k ≠ 0 := by
    intro h
    have hh : c.levelEmbedding k = c.levelEmbedding 0 := by simpa only [c.levelEmbedding_zero] using h
    exact hk (c.levelEmbedding.injective hh)
  have hmem : c.levelEmbedding k ∈ c.levelSet := (c.levelIso k).property
  simp only [Code.levelSet,Finset.mem_insert,Finset.mem_union,Finset.mem_image,
    Finset.mem_univ,true_and] at hmem
  rcases hmem with hz | ⟨j,hj⟩ | ⟨j,hj⟩
  · exact False.elim (hzero hz)
  · refine ⟨j,Or.inl ?_⟩
    apply c.levelEmbedding.injective
    rw [c.recover_d]
    exact hj
  · refine ⟨j,Or.inr ?_⟩
    apply c.levelEmbedding.injective
    rw [c.recover_y]
    exact hj

 theorem Code.levelCount_le (c : Code i m) : c.levelCount ≤ 2*i :=
  normalized_size_le c.normalize c.normalize_isNormalized

 theorem Code.normalize_admissible_iff (c : Code i m) :
    c.normalize.IsAdmissible ↔ c.IsAdmissible := by
  have hh := finite_recoding_admissible_iff c.levelEmbedding c.levelEmbedding_zero
    c.normalize.d c.normalize.y c.epsilon c.normalize.monotone_d
  have hd : (fun j => c.levelEmbedding (c.normalize.d j)) = c.d := funext c.recover_d
  have hy : (fun j => c.levelEmbedding (c.normalize.y j)) = c.y := funext c.recover_y
  rw [hd,hy] at hh
  exact hh.symm

end
end CokernelPolynomiality
