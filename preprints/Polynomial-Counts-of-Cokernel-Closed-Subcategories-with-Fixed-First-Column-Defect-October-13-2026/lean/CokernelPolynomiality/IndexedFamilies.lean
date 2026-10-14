import CokernelPolynomiality.FamilyLifts

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

variable {I J : Type} [Fintype I] [Fintype J]

def indexedFamily (n : ℕ) (c d : I → ℕ) : ChainRep.{0} n where
  obj i := FGModuleCat.of ℂ (∀j,intervalSpace (c j) (d j) i.ofDual.val)
  map {i k} _ := FGModuleCat.ofHom (LinearMap.pi (fun j =>
    (intervalMap (c j) (d j) k.ofDual.val i.ofDual.val).comp (LinearMap.proj j)))
  map_id i := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    exact congrArg (fun f => f (x j)) (intervalMap_id (c j) (d j) i.ofDual.val)
  map_comp {i j k} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    exact (congrArg (fun h => h (x t))
      (intervalMap_comp (c t) (d t) k.ofDual.val j.ofDual.val i.ofDual.val (leOfHom g) (leOfHom f))).symm

def indexedFamilyReindex (n : ℕ) (c d : I → ℕ) (e : I ≃ J) :
    indexedFamily n c d ≅ indexedFamily n (c ∘ e.symm) (d ∘ e.symm) :=
  NatIso.ofComponents (fun i => (LinearEquiv.piCongrLeft' ℂ
    (fun j => intervalSpace (c j) (d j) i.ofDual.val) e).toFGModuleCatIso) (by
      intro i k f
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext j
      rfl)

def indexedFamilySum (n : ℕ) (c d : I ⊕ J → ℕ) :
    indexedFamily n c d ≅ directPair (indexedFamily n (c ∘ Sum.inl) (d ∘ Sum.inl))
      (indexedFamily n (c ∘ Sum.inr) (d ∘ Sum.inr)) :=
  NatIso.ofComponents (fun i => (LinearEquiv.sumPiEquivProdPi ℂ I J
    (fun j => intervalSpace (c j) (d j) i.ofDual.val)).toFGModuleCatIso) (by
      intro i k f
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def intervalFamilyConcatIso (n m k : ℕ) (c d : Fin m → ℕ) (c' d' : Fin k → ℕ) :
    intervalFamily n (m+k) (Sum.elim c c' ∘ finSumFinEquiv.symm)
      (Sum.elim d d' ∘ finSumFinEquiv.symm) ≅
      biprod (intervalFamily n m c d) (intervalFamily n k c' d') :=
  (indexedFamilyReindex n (Sum.elim c c') (Sum.elim d d') finSumFinEquiv).symm ≪≫
    indexedFamilySum n (Sum.elim c c') (Sum.elim d d') ≪≫
      directPairIsoBiprod _ _

end CokernelPolynomiality
