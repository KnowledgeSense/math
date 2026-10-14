import CokernelPolynomiality.FamilyLifts
import Mathlib.CategoryTheory.Linear.FunctorCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem intervalFamily_hom_ext {n m : ℕ} {V : ChainRep.{0} n} {c d : Fin m → ℕ}
    {f g : V ⟶ intervalFamily n m c d}
    (h : ∀ j, f ≫ intervalFamilyProj n m c d j=g ≫ intervalFamilyProj n m c d j) : f=g := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext j
  exact congrArg (fun t => (t.app i).hom.hom x) (h j)

@[simp] theorem intervalFamilyLift_proj {n m : ℕ} {V : ChainRep.{0} n} {c d : Fin m → ℕ}
    (f : ∀ j, V ⟶ intervalRep n (c j) (d j)) (j : Fin m) :
    intervalFamilyLift f ≫ intervalFamilyProj n m c d j=f j := by
  apply NatTrans.ext
  funext i
  rfl

def familyDiagonal {n m : ℕ} (c d : Fin m → ℕ) (s : Fin m → ℂ) :
    intervalFamily n m c d ⟶ intervalFamily n m c d :=
  intervalFamilyLift (fun j => s j • intervalFamilyProj n m c d j)

@[simp] theorem familyDiagonal_proj {n m : ℕ} (c d : Fin m → ℕ) (s : Fin m → ℂ) (j : Fin m) :
    familyDiagonal (n:=n) c d s ≫ intervalFamilyProj n m c d j=
      s j • intervalFamilyProj n m c d j := intervalFamilyLift_proj _ _

def familyDiagonalIso {n m : ℕ} (c d : Fin m → ℕ) (s : Fin m → ℂ) (hs : ∀ j, s j ≠ 0) :
    intervalFamily n m c d ≅ intervalFamily n m c d where
  hom := familyDiagonal c d s
  inv := familyDiagonal c d (fun j => (s j)⁻¹)
  hom_inv_id := by
    apply intervalFamily_hom_ext
    intro j
    simp only [Category.assoc,familyDiagonal_proj,Linear.comp_smul,smul_smul,Category.id_comp]
    rw [inv_mul_cancel₀ (hs j),one_smul]
  inv_hom_id := by
    apply intervalFamily_hom_ext
    intro j
    simp only [Category.assoc,familyDiagonal_proj,Linear.comp_smul,smul_smul,Category.id_comp]
    rw [mul_inv_cancel₀ (hs j),one_smul]

def squareZeroShearIso {n : ℕ} {V : ChainRep.{0} n} (N : V ⟶ V) (hN : N ≫ N=0) : V ≅ V where
  hom := 𝟙 V-N
  inv := 𝟙 V+N
  hom_inv_id := by
    simp only [Preadditive.sub_comp,Preadditive.comp_add,Category.id_comp,Category.comp_id,hN]
    abel
  inv_hom_id := by
    simp only [Preadditive.add_comp,Preadditive.comp_sub,Category.id_comp,Category.comp_id,hN]
    abel

end CokernelPolynomiality
