import CokernelPolynomiality.DirectPairs
import Mathlib.LinearAlgebra.Pi

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

/-- A literal finite pointwise direct sum of interval representations. -/
def intervalFamily (n m : ℕ) (c d : Fin m → ℕ) : ChainRep.{0} n where
  obj i := FGModuleCat.of ℂ (∀ j : Fin m, intervalSpace (c j) (d j) i.ofDual.val)
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

def intervalFamilyProj (n m : ℕ) (c d : Fin m → ℕ) (j : Fin m) :
    intervalFamily n m c d ⟶ intervalRep n (c j) (d j) where
  app _ := FGModuleCat.ofHom (LinearMap.proj j)
  naturality {_i _k} _f := rfl

def intervalFamilyInj (n m : ℕ) (c d : Fin m → ℕ) (j : Fin m) :
    intervalRep n (c j) (d j) ⟶ intervalFamily n m c d where
  app i := FGModuleCat.ofHom (LinearMap.single ℂ (fun k => intervalSpace (c k) (d k) i.ofDual.val) j)
  naturality {i k} f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change intervalSpace (c j) (d j) i.ofDual.val at x
    funext t
    change (Pi.single j (intervalMap (c j) (d j) k.ofDual.val i.ofDual.val x) :
      ∀ t, intervalSpace (c t) (d t) k.ofDual.val) t =
      intervalMap (c t) (d t) k.ofDual.val i.ofDual.val
        ((Pi.single j x : ∀ t, intervalSpace (c t) (d t) i.ofDual.val) t)
    by_cases ht : t=j
    · subst t
      simp
    · simp [ht]

@[simp] theorem intervalFamily_inj_proj (n m : ℕ) (c d : Fin m → ℕ) (j : Fin m) :
    intervalFamilyInj n m c d j ≫ intervalFamilyProj n m c d j=𝟙 _ := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  exact LinearMap.proj_comp_single_same ℂ (fun t => intervalSpace (c t) (d t) i.ofDual.val) j

@[simp] theorem intervalFamily_inj_proj_ne (n m : ℕ) (c d : Fin m → ℕ)
    (j k : Fin m) (hjk : k ≠ j) :
    intervalFamilyInj n m c d j ≫ intervalFamilyProj n m c d k=0 := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  exact LinearMap.proj_comp_single_ne ℂ (fun t => intervalSpace (c t) (d t) i.ofDual.val) k j hjk

theorem intervalFamily_total (n m : ℕ) (c d : Fin m → ℕ) :
    (∑ j : Fin m, intervalFamilyProj n m c d j ≫ intervalFamilyInj n m c d j)=
      𝟙 (intervalFamily n m c d) := by
  apply NatTrans.ext
  funext i
  rw [NatTrans.app_sum]
  apply FGModuleCat.hom_ext
  let F := forget₂ (FGModuleCat.{0} ℂ) (ModuleCat.{0} ℂ)
  change (F.map (∑ j : Fin m, (intervalFamilyProj n m c d j ≫ intervalFamilyInj n m c d j).app i)).hom = _
  rw [Functor.map_sum,ModuleCat.hom_sum]
  apply LinearMap.ext
  intro x
  change (∀ t, intervalSpace (c t) (d t) i.ofDual.val) at x
  funext k
  change (∑ j : Fin m, (LinearMap.single ℂ (fun t => intervalSpace (c t) (d t) i.ofDual.val) j).comp
    (LinearMap.proj j)) x k=x k
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
  have hh := congrFun (LinearMap.sum_single_apply (fun t => intervalSpace (c t) (d t) i.ofDual.val) x) k
  simpa only [LinearMap.sum_apply,Finset.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.single_apply] using hh

end CokernelPolynomiality
