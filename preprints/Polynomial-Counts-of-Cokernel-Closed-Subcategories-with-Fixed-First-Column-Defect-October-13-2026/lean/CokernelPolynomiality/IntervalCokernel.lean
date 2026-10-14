import CokernelPolynomiality.RepresentationSubcategories
import CokernelPolynomiality.IntervalCokernelLinear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def intervalCokernelProjection (n _a b c d : ℕ) (hcb : c ≤ b) :
    intervalRep n c d ⟶ intervalRep n (b+1) d :=
  intervalHom n c d (b+1) d (by omega) (le_refl d)

theorem intervalHom_projection_zero (n a b c d : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) :
    intervalHom n a b c d hac hbd ≫ intervalCokernelProjection n a b c d hcb=0 := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  ext x
  exact (intervalCokernel_exact a b c d i.ofDual.val hac).apply_apply_eq_zero x

def fgCokernelIsColimit {X Y Z : FGModuleCat.{0} ℂ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hzero : f ≫ g=0) (hex : Function.Exact f.hom.hom g.hom.hom)
    (hsurj : Function.Surjective g.hom.hom) : IsColimit (CokernelCofork.ofπ g hzero) := by
  let F := forget₂ (FGModuleCat.{0} ℂ) (ModuleCat.{0} ℂ)
  apply isColimitOfReflects F
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  exact ModuleCat.isColimitCokernelCofork f.hom g.hom hex hsurj

/-- The genuine categorical cokernel of the canonical interval morphism. -/
def intervalCokernelIsColimit (n a b c d : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) :
    IsColimit (CokernelCofork.ofπ (intervalCokernelProjection n a b c d hcb)
      (intervalHom_projection_zero n a b c d hac hcb hbd)) := by
  apply evaluationJointlyReflectsColimits
  intro i
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  have hz := congrArg (fun f => f.app i) (intervalHom_projection_zero n a b c d hac hcb hbd)
  exact fgCokernelIsColimit _ _ hz (intervalCokernel_exact a b c d i.ofDual.val hac)
    (intervalProjection_surjective c b d i.ofDual.val (by omega))

def intervalCokernelIso (n a b c d : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) :
    cokernel (intervalHom n a b c d hac hbd) ≅ intervalRep n (b+1) d :=
  colimit.isoColimitCocone ⟨_,intervalCokernelIsColimit n a b c d hac hcb hbd⟩

theorem CokernelSubcategory.interval_cokernel_mem {n a b c d : ℕ} (C : CokernelSubcategory n)
    (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d)
    (hA : C.contains (intervalRep n a b)) (hB : C.contains (intervalRep n c d)) :
    C.contains (intervalRep n (b+1) d) :=
  C.iso_closed (intervalCokernelIso n a b c d hac hcb hbd)
    (C.cokernel_mem (intervalHom n a b c d hac hbd) hA hB)

end CokernelPolynomiality
