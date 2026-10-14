import CokernelPolynomiality.IntervalHomOrder
import Mathlib.CategoryTheory.Linear.FunctorCategory

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

def intervalGenerator (a b : ℕ) (hab : a ≤ b) : intervalSpace a b b :=
  ⟨1,by simp [intervalSpace,intervalActive,hab]⟩

def intervalScalar {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (hab : a ≤ b) (hbn : b ≤ n) : ℂ :=
  (intervalApp f (OrderDual.toDual ⟨b,by omega⟩) (intervalGenerator a b hab)).val

theorem intervalApp_scalar {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (hab : a ≤ b) (hbn : b ≤ n) (i : (Fin (n+1))ᵒᵈ)
    (x : intervalSpace a b i.ofDual.val) :
    (intervalApp f i x).val =
      if intervalActive c d i.ofDual.val then x.val*intervalScalar f hab hbn else 0 := by
  by_cases ht : intervalActive c d i.ofDual.val
  · rw [ite_eq_left ht]
    by_cases hs : intervalActive a b i.ofDual.val
    · let j : (Fin (n+1))ᵒᵈ := OrderDual.toDual ⟨b,by omega⟩
      let y : intervalSpace a b b := x.val • intervalGenerator a b hab
      have hy : intervalMap a b i.ofDual.val b y=x := by
        apply Subtype.ext
        simp [intervalMap_val,hs,y,intervalGenerator]
      have hh := intervalNaturality_val f i j hs.2 y
      change (intervalApp f i (intervalMap a b i.ofDual.val b y)).val =
        (if intervalActive c d i.ofDual.val then (intervalApp f j y).val else 0) at hh
      rw [hy,ite_eq_left ht] at hh
      rw [hh]
      change (intervalApp f j (x.val • intervalGenerator a b hab)).val = _
      exact congrArg Subtype.val ((intervalApp f j).map_smul x.val (intervalGenerator a b hab))
    · have hx : x=0 := Subtype.ext (intervalSpace_val_zero hs x)
      rw [hx,map_zero]
      simp
  · rw [ite_eq_right ht]
    exact intervalSpace_val_zero ht (intervalApp f i x)

/-- Every interval morphism is an actual scalar multiple of the canonical
morphism, with no unproved representation-theoretic Hom-space formula. -/
theorem intervalHom_eq_scalar {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d) (hbn : b ≤ n) :
    f=intervalScalar f (hac.trans hcb) hbn • intervalHom n a b c d hac hbd := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change intervalSpace a b i.ofDual.val at x
  apply Subtype.ext
  change (intervalApp f i x).val =
    intervalScalar f (hac.trans hcb) hbn * (intervalComponent a b c d i.ofDual.val x).val
  rw [intervalApp_scalar f (hac.trans hcb) hbn,intervalComponent_val]
  split <;> ring

end CokernelPolynomiality
