import CokernelPolynomiality.IntervalFamilies

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def intervalFamilyLift {n m : ℕ} {V : ChainRep.{0} n} {c d : Fin m → ℕ}
    (f : ∀ j, V ⟶ intervalRep n (c j) (d j)) : V ⟶ intervalFamily n m c d where
  app i := FGModuleCat.ofHom (LinearMap.pi (fun j => ((f j).app i).hom.hom))
  naturality {i k} g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    exact congrArg (fun h => h.hom.hom x) ((f j).naturality g)

@[simp] theorem intervalFamilyLift_app {n m : ℕ} {V : ChainRep.{0} n} {c d : Fin m → ℕ}
    (f : ∀ j, V ⟶ intervalRep n (c j) (d j)) (i) (x : V.obj i) (j : Fin m) :
    ((intervalFamilyLift f).app i).hom.hom x j=((f j).app i).hom.hom x := rfl

end CokernelPolynomiality
