import CokernelPolynomiality.DirectPairs
import CokernelPolynomiality.IntervalCokernel
import CokernelPolynomiality.PairCokernelLinear

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def pairSource (n a b c d e f : ℕ) (hac : a ≤ c) (hbd : b ≤ d)
    (hae : a ≤ e) (hbf : b ≤ f) :
    intervalRep n a b ⟶ directPair (intervalRep n c d) (intervalRep n e f) :=
  directPairLift (intervalHom n a b c d hac hbd) (intervalHom n a b e f hae hbf)

def pairProjection (n b c d e f : ℕ) (hcb : c ≤ b) (hdf : d ≤ f) :
    directPair (intervalRep n c d) (intervalRep n e f) ⟶
      directPair (intervalRep n (b+1) d) (intervalRep n (max c e) f) :=
  directPairLift
    (directPairFst _ _ ≫ intervalHom n c d (b+1) d (by omega) (le_refl d))
    ((directPairFst _ _ ≫ intervalHom n c d (max c e) f (le_max_left c e) hdf)-
      (directPairSnd _ _ ≫ intervalHom n e f (max c e) f (le_max_right c e) (le_refl f)))

theorem pairSource_app (n a b c d e f : ℕ) (hac : a ≤ c) (hbd : b ≤ d)
    (hae : a ≤ e) (hbf : b ≤ f) (i : (Fin (n+1))ᵒᵈ) :
    ((pairSource n a b c d e f hac hbd hae hbf).app i).hom.hom=
      pairIntervalSource a b c d e f i.ofDual.val := rfl

theorem pairProjection_app (n b c d e f : ℕ) (hcb : c ≤ b) (hdf : d ≤ f)
    (i : (Fin (n+1))ᵒᵈ) :
    ((pairProjection n b c d e f hcb hdf).app i).hom.hom=
      pairIntervalQuotient b c d e f i.ofDual.val := rfl

theorem pairSource_projection_zero (n a b c d e f : ℕ)
    (hac : a ≤ c) (hae : a ≤ e) (hcb : c ≤ b) (heb : e ≤ b)
    (hbd : b ≤ d) (hdf : d ≤ f) :
    pairSource n a b c d e f hac hbd hae (hbd.trans hdf) ≫
      pairProjection n b c d e f hcb hdf=0 := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (pairIntervalQuotient_exact a b c d e f i.ofDual.val hac hae hcb heb hbd hdf).apply_apply_eq_zero x

def pairCokernelIsColimit (n a b c d e f : ℕ)
    (hac : a ≤ c) (hae : a ≤ e) (hcb : c ≤ b) (heb : e ≤ b)
    (hbd : b ≤ d) (hdf : d ≤ f) :
    IsColimit (CokernelCofork.ofπ (pairProjection n b c d e f hcb hdf)
      (pairSource_projection_zero n a b c d e f hac hae hcb heb hbd hdf)) := by
  apply evaluationJointlyReflectsColimits
  intro i
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  have hz := congrArg (fun g => g.app i)
    (pairSource_projection_zero n a b c d e f hac hae hcb heb hbd hdf)
  exact fgCokernelIsColimit _ _ hz
    (pairIntervalQuotient_exact a b c d e f i.ofDual.val hac hae hcb heb hbd hdf)
    (pairIntervalQuotient_surjective b c d e f i.ofDual.val hcb heb hbd hdf)

def pairCokernelIso (n a b c d e f : ℕ)
    (hac : a ≤ c) (hae : a ≤ e) (hcb : c ≤ b) (heb : e ≤ b)
    (hbd : b ≤ d) (hdf : d ≤ f) :
    cokernel (pairSource n a b c d e f hac hbd hae (hbd.trans hdf)) ≅
      directPair (intervalRep n (b+1) d) (intervalRep n (max c e) f) :=
  colimit.isoColimitCocone ⟨_,pairCokernelIsColimit n a b c d e f hac hae hcb heb hbd hdf⟩

end CokernelPolynomiality
