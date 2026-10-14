import CokernelPolynomiality.IntervalMorphisms

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

def intervalApp {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (i : (Fin (n+1))ᵒᵈ) : intervalSpace a b i.ofDual.val →ₗ[ℂ] intervalSpace c d i.ofDual.val :=
  (f.app i).hom.hom

theorem intervalNaturality_val {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (i j : (Fin (n+1))ᵒᵈ) (hij : i.ofDual.val ≤ j.ofDual.val)
    (x : intervalSpace a b j.ofDual.val) :
    ((intervalApp f i) (intervalMap a b i.ofDual.val j.ofDual.val x)).val =
      if intervalActive c d i.ofDual.val then ((intervalApp f j) x).val else 0 := by
  have h := f.naturality (homOfLE (X:=(Fin (n+1))ᵒᵈ) (x:=j) (y:=i) hij)
  have hh := congrArg (fun g => ((g.hom.hom) x).val) h
  change ((intervalApp f i) (intervalMap a b i.ofDual.val j.ofDual.val x)).val =
    (intervalMap c d i.ofDual.val j.ofDual.val ((intervalApp f j) x)).val at hh
  rwa [intervalMap_val] at hh

theorem nonzero_intervalHom_witness {n a b c d : ℕ}
    (f : intervalRep n a b ⟶ intervalRep n c d) (hf : f ≠ 0) :
    ∃ (i : (Fin (n+1))ᵒᵈ) (x : intervalSpace a b i.ofDual.val),
      ((intervalApp f i) x).val ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hf
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  ext x
  apply Subtype.ext
  exact hn i x

/-- Nonzero maps between literal interval representations have precisely the
source's endpoint order; in particular maps both ways force equal endpoints. -/
theorem intervalHom_order_of_ne_zero {n a b c d : ℕ}
    (f : intervalRep n a b ⟶ intervalRep n c d) (hf : f ≠ 0)
    (hbn : b ≤ n) : a ≤ c ∧ c ≤ b ∧ b ≤ d := by
  obtain ⟨i,x,hx⟩ := nonzero_intervalHom_witness f hf
  have hiS : intervalActive a b i.ofDual.val := by
    by_contra h
    have hz : x=0 := Subtype.ext (intervalSpace_val_zero h x)
    simp [hz] at hx
  have hiT : intervalActive c d i.ofDual.val := by
    by_contra h
    exact hx (intervalSpace_val_zero h ((intervalApp f i) x))
  have hcb : c ≤ b := hiT.1.trans hiS.2
  have hac : a ≤ c := by
    by_contra h
    have hca : c < a := by omega
    let j : (Fin (n+1))ᵒᵈ := OrderDual.toDual ⟨c,by omega⟩
    have hjS : ¬intervalActive a b c := by unfold intervalActive; omega
    have hjT : intervalActive c d c := ⟨le_refl c,le_trans hiT.1 hiT.2⟩
    have hh := intervalNaturality_val f j i hiT.1 x
    have hz : intervalMap a b c i.ofDual.val x=0 := by
      apply Subtype.ext
      simp [intervalMap_val,hjS]
    change ((intervalApp f j) (intervalMap a b c i.ofDual.val x)).val =
      if intervalActive c d c then ((intervalApp f i) x).val else 0 at hh
    rw [hz,ite_eq_left hjT] at hh
    exact hx (hh.symm.trans (congrArg Subtype.val (map_zero (intervalApp f j))))
  have hbd : b ≤ d := by
    by_contra h
    have hdb : d < b := by omega
    let j : (Fin (n+1))ᵒᵈ := OrderDual.toDual ⟨b,by omega⟩
    have hjS : intervalActive a b b := ⟨hiS.1.trans hiS.2,le_refl b⟩
    have hjT : ¬intervalActive c d b := by unfold intervalActive; omega
    let y : intervalSpace a b b := ⟨x.val,by simp [intervalSpace,hjS]⟩
    have hh := intervalNaturality_val f i j hiS.2 y
    have hy : intervalMap a b i.ofDual.val b y=x := by
      apply Subtype.ext
      simp [intervalMap_val,hiS,y]
    change (intervalApp f i (intervalMap a b i.ofDual.val b y)).val =
      (if intervalActive c d i.ofDual.val then (intervalApp f j y).val else 0) at hh
    rw [hy,ite_eq_left hiT] at hh
    exact hx (hh.trans (intervalSpace_val_zero hjT ((intervalApp f j) y)))
  exact ⟨hac,hcb,hbd⟩

end CokernelPolynomiality
