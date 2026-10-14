import CokernelPolynomiality.FamilyLifts
import CokernelPolynomiality.AntichainExact
import CokernelPolynomiality.IntervalCokernel

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def antichainSourceHom {m : ℕ} (n a b : ℕ) (c d : Fin (m+1) → ℕ)
    (hac : ∀ j, a ≤ c j) (hbd : ∀ j, b ≤ d j) :
    intervalRep n a b ⟶ intervalFamily n (m+1) c d :=
  intervalFamilyLift (fun j => intervalHom n a b (c j) (d j) (hac j) (hbd j))

def antichainProjection {m : ℕ} (n b : ℕ) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hcb : ∀ j, c j ≤ b) :
    intervalFamily n (m+1) c d ⟶ intervalFamily n (m+1) (antichainOutputStart b c) d :=
  intervalFamilyLift (fun j =>
    (intervalFamilyProj n (m+1) c d j ≫
      intervalHom n (c j) (d j) (antichainOutputStart b c j) (d j)
        (antichainOutputStart_ge b c hc hcb j j le_rfl) le_rfl)-
    if h : j.val < m then
      intervalFamilyProj n (m+1) c d ⟨j.val+1,by omega⟩ ≫
        intervalHom n (c ⟨j.val+1,by omega⟩) (d ⟨j.val+1,by omega⟩)
          (antichainOutputStart b c j) (d j)
          ((antichainOutputStart_castSucc b c ⟨j.val,h⟩).symm.le)
          (hd (by change j.val ≤ j.val+1; omega))
    else 0)

theorem antichainSourceHom_app {m : ℕ} (n a b : ℕ) (c d : Fin (m+1) → ℕ)
    (hac : ∀ j, a ≤ c j) (hbd : ∀ j, b ≤ d j) (i : (Fin (n+1))ᵒᵈ) :
    ((antichainSourceHom n a b c d hac hbd).app i).hom.hom=
      antichainSource a b c d i.ofDual.val := rfl

set_option backward.isDefEq.respectTransparency false in
theorem antichainProjection_app {m : ℕ} (n b : ℕ) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hcb : ∀ j, c j ≤ b) (i : (Fin (n+1))ᵒᵈ) :
    ((antichainProjection n b c d hc hd hcb).app i).hom.hom=
      antichainQuotient b c d i.ofDual.val := by
  apply LinearMap.ext
  intro x
  change (∀ t, intervalSpace (c t) (d t) i.ofDual.val) at x
  funext j
  change _ = ((intervalComponent (c j) (d j) (antichainOutputStart b c j) (d j) i.ofDual.val).comp
    (LinearMap.proj j : (∀ t, intervalSpace (c t) (d t) i.ofDual.val) →ₗ[ℂ] _)-
    if h : j.val < m then
      (intervalComponent (c ⟨j.val+1,by omega⟩) (d ⟨j.val+1,by omega⟩)
        (antichainOutputStart b c j) (d j) i.ofDual.val).comp
        (LinearMap.proj ⟨j.val+1,by omega⟩ : (∀ t, intervalSpace (c t) (d t) i.ofDual.val) →ₗ[ℂ] _)
    else 0) x
  by_cases h : j.val < m
  · simp only [antichainProjection,intervalFamilyLift_app,dite_eq_left h]
    rfl
  · simp only [antichainProjection,intervalFamilyLift_app,dite_eq_right h]
    rfl

theorem antichainSource_projection_zero {m : ℕ} (n a b : ℕ) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) :
    antichainSourceHom n a b c d hac hbd ≫ antichainProjection n b c d hc hd hcb=0 := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((antichainProjection n b c d hc hd hcb).app i).hom.hom
    (((antichainSourceHom n a b c d hac hbd).app i).hom.hom x)=0
  rw [antichainProjection_app,antichainSourceHom_app]
  exact (antichainQuotient_exact a b c d i.ofDual.val hc hac hcb hbd).apply_apply_eq_zero x

def antichainCokernelIsColimit {m : ℕ} (n a b : ℕ) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) :
    IsColimit (CokernelCofork.ofπ (antichainProjection n b c d hc hd hcb)
      (antichainSource_projection_zero n a b c d hc hd hac hcb hbd)) := by
  apply evaluationJointlyReflectsColimits
  intro i
  apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  have hz := congrArg (fun g => g.app i)
    (antichainSource_projection_zero n a b c d hc hd hac hcb hbd)
  apply fgCokernelIsColimit _ _ hz
  · rw [antichainSourceHom_app,antichainProjection_app]
    exact antichainQuotient_exact a b c d i.ofDual.val hc hac hcb hbd
  · rw [antichainProjection_app]
    exact antichainQuotient_surjective b c d i.ofDual.val hc hd hcb

def antichainCokernelIso {m : ℕ} (n a b : ℕ) (c d : Fin (m+1) → ℕ)
    (hc : Monotone c) (hd : Antitone d) (hac : ∀ j, a ≤ c j)
    (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) :
    cokernel (antichainSourceHom n a b c d hac hbd) ≅
      intervalFamily n (m+1) (antichainOutputStart b c) d :=
  colimit.isoColimitCocone ⟨_,antichainCokernelIsColimit n a b c d hc hd hac hcb hbd⟩

end CokernelPolynomiality
