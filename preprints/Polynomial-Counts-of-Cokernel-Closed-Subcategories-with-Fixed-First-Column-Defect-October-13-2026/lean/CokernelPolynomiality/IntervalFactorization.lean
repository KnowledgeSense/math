import CokernelPolynomiality.IntervalScalars

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

theorem intervalHom_comp (n a b c d e f : ℕ) (hac : a ≤ c) (hce : c ≤ e)
    (hbd : b ≤ d) (hdf : d ≤ f) :
    intervalHom n a b c d hac hbd ≫ intervalHom n c d e f hce hdf=
      intervalHom n a b e f (hac.trans hce) (hbd.trans hdf) := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change intervalSpace a b i.ofDual.val at x
  apply Subtype.ext
  change (intervalComponent c d e f i.ofDual.val
    (intervalComponent a b c d i.ofDual.val x)).val =
      (intervalComponent a b e f i.ofDual.val x).val
  rw [intervalComponent_val,intervalComponent_val,intervalComponent_val]
  by_cases ht : intervalActive e f i.ofDual.val
  · rw [ite_eq_left ht,ite_eq_left ht]
    by_cases hs : intervalActive a b i.ofDual.val
    · rw [ite_eq_left ⟨hce.trans ht.1,hs.2.trans hbd⟩]
    · rw [intervalSpace_val_zero hs x]
      split <;> rfl
  · rw [ite_eq_right ht,ite_eq_right ht]

theorem intervalScalar_ne_zero {n a b c d : ℕ} (f : intervalRep n a b ⟶ intervalRep n c d)
    (hab : a ≤ b) (hbn : b ≤ n) (hf : f ≠ 0) : intervalScalar f hab hbn ≠ 0 := by
  obtain ⟨hac,hcb,hbd⟩ := intervalHom_order_of_ne_zero f hf hbn
  intro hs
  apply hf
  rw [intervalHom_eq_scalar f hac hcb hbd hbn,hs,zero_smul]

theorem interval_factor_through {n a b c d e f : ℕ}
    (p : intervalRep n a b ⟶ intervalRep n c d)
    (q : intervalRep n a b ⟶ intervalRep n e f)
    (hab : a ≤ b) (hbn : b ≤ n) (hp : p ≠ 0) (hq : q ≠ 0)
    (hce : c ≤ e) (hdf : d ≤ f) :
    p ≫ ((intervalScalar q hab hbn / intervalScalar p hab hbn) • intervalHom n c d e f hce hdf)=q := by
  obtain ⟨hac,hcb,hbd⟩ := intervalHom_order_of_ne_zero p hp hbn
  obtain ⟨hae,heb,hbf⟩ := intervalHom_order_of_ne_zero q hq hbn
  have hsp := intervalScalar_ne_zero p hab hbn hp
  conv_lhs => lhs; rw [intervalHom_eq_scalar p hac hcb hbd hbn]
  conv_rhs => rw [intervalHom_eq_scalar q hae heb hbf hbn]
  simp only [Linear.smul_comp,Linear.comp_smul,smul_smul,intervalHom_comp]
  congr 1
  field_simp

end CokernelPolynomiality
