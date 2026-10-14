import CokernelPolynomiality.Normalization

namespace CokernelPolynomiality
noncomputable section

variable {i q r m : ℕ}

 def Code.recode (c : Code i q) (e : Fin (q+1) ↪o Fin (m+1)) : Code i m where
  d j := e (c.d j)
  y j := e (c.y j)
  epsilon := c.epsilon
  monotone_d := e.monotone.comp c.monotone_d

 theorem Code.recode_admissible_iff (c : Code i q) (e : Fin (q+1) ↪o Fin (m+1))
    (he : e 0 = 0) : (c.recode e).IsAdmissible ↔ c.IsAdmissible :=
  finite_recoding_admissible_iff e he c.d c.y c.epsilon c.monotone_d

 theorem Code.normalize_recovery (c : Code i m) : c.normalize.recode c.levelEmbedding = c := by
  apply Code.data_injective i m
  simp only [Code.recode]
  exact Prod.ext (funext c.recover_d) (Prod.ext (funext c.recover_y) rfl)

 theorem Code.recode_levelSet (c : Code i q) (hc : c.IsNormalized)
    (e : Fin (q+1) ↪o Fin (m+1)) (he : e 0 = 0) :
    (c.recode e).levelSet = Finset.univ.image e := by
  classical
  ext v
  simp only [Code.levelSet,Code.recode,Finset.mem_insert,Finset.mem_union,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (hv | ⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨0,he.trans hv.symm⟩
    · exact ⟨c.d j,hj⟩
    · exact ⟨c.y j,hj⟩
  · rintro ⟨k,rfl⟩
    by_cases hk : k = 0
    · subst k
      exact Or.inl he
    · obtain ⟨j,hj⟩ := hc k hk
      rcases hj with hd | hy
      · exact Or.inr (Or.inl ⟨j,congrArg e hd⟩)
      · exact Or.inr (Or.inr ⟨j,congrArg e hy⟩)

 theorem Code.recode_levelCount (c : Code i q) (hc : c.IsNormalized)
    (e : Fin (q+1) ↪o Fin (m+1)) (he : e 0 = 0) :
    (c.recode e).levelCount = q := by
  unfold Code.levelCount
  rw [c.recode_levelSet hc e he,Finset.card_image_of_injective _ e.injective]
  simp

 theorem normalized_factorization_size_unique (c : Code i q) (hc : c.IsNormalized)
    (c' : Code i r) (hc' : c'.IsNormalized)
    (e : Fin (q+1) ↪o Fin (m+1)) (he : e 0 = 0)
    (e' : Fin (r+1) ↪o Fin (m+1)) (he' : e' 0 = 0)
    (h : c.recode e = c'.recode e') : q = r := by
  have hh := congrArg Code.levelCount h
  rw [c.recode_levelCount hc e he,c'.recode_levelCount hc' e' he'] at hh
  exact hh

 theorem normalized_factorization_embedding_unique (c c' : Code i q)
    (hc : c.IsNormalized) (hc' : c'.IsNormalized)
    (e e' : Fin (q+1) ↪o Fin (m+1)) (he : e 0 = 0) (he' : e' 0 = 0)
    (h : c.recode e = c'.recode e') : e = e' := by
  classical
  have hs : Finset.univ.image e = Finset.univ.image e' := by
    rw [← c.recode_levelSet hc e he,← c'.recode_levelSet hc' e' he',h]
  let S := Finset.univ.image e
  have hcard : S.card = q+1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hfirst : e = S.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique' hcard (fun j => Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  have hsecond : e' = S.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique' hcard
    intro j
    dsimp [S]
    rw [hs]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  exact hfirst.trans hsecond.symm

 theorem Code.recode_injective (e : Fin (q+1) ↪o Fin (m+1)) :
    Function.Injective (fun c : Code i q => c.recode e) := by
  intro c c' h
  apply Code.data_injective i q
  have hd := congrArg Code.d h
  have hy := congrArg Code.y h
  have he := congrArg Code.epsilon h
  apply Prod.ext
  · funext j
    exact e.injective (congrFun hd j)
  · apply Prod.ext
    · funext j
      exact e.injective (congrFun hy j)
    · exact he

end
end CokernelPolynomiality
