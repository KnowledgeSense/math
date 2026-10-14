import Fan.InvariantUniquenessSymmetry

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

omit [DecidableLE α] in
theorem incidence_rightInverse_of_leftInverse {R : Type*} [CommRing R]
    (p q : IncidenceAlgebra R α) (hp : ∀ x,p x x=1) (hqp : q*p=1) : p*q=1 := by
  have haux : (q+(1-p*q))*p=1 := by
    rw [add_mul,sub_mul,one_mul,mul_assoc,hqp,mul_one,sub_self,add_zero]
  have he := incidence_leftInverse_unique p q (q+(1-p*q)) hp hqp haux
  have hz : (0:IncidenceAlgebra R α)=1-p*q :=
    add_left_cancel (show q+0=q+(1-p*q) by simpa only [add_zero] using he)
  exact (sub_eq_zero.mp hz.symm).symm

def zKernel (r : α→ℕ) : IncidenceAlgebra (Polynomial ℤ) α := rankZeta r*klKernel r

def signedInverseZKernel (r : α→ℕ) : IncidenceAlgebra (Polynomial ℤ) α := klInverseKernel r*rankMu r

theorem zKernel_apply (r : α→ℕ) (a b : α) :
    zKernel r a b=∑ x∈Icc a b,X^(r x-r a)*kl r b x := by
  rw [zKernel,mul_apply]
  apply sum_congr rfl
  intro x hx
  change (IncidenceAlgebra.zeta (Polynomial ℤ) a x*X^(r x-r a))*kl r b x=_
  rw [zeta_of_le (mem_Icc.mp hx).1,one_mul]

theorem zKernel_diag (r : α→ℕ) (a : α) : zKernel r a a=1 := by
  rw [zKernel_apply]
  simp

theorem signedInverseZKernel_mul_zKernel (r : α→ℕ) (hr : Monotone r) :
    signedInverseZKernel r*zKernel r=1 := by
  unfold signedInverseZKernel zKernel
  calc
    _ = klInverseKernel r*(rankMu r*rankZeta r)*klKernel r := by simp only [mul_assoc]
    _ = 1 := by rw [rankMu_mul_rankZeta r hr,mul_one,klInverseKernel_mul_klKernel]

theorem zKernel_mul_signedInverseZKernel (r : α→ℕ) (hr : Monotone r) :
    zKernel r*signedInverseZKernel r=1 :=
  incidence_rightInverse_of_leftInverse _ _ (zKernel_diag r) (signedInverseZKernel_mul_zKernel r hr)

omit [LocallyFiniteOrder α] [DecidableEq α] in
theorem rankZeta_rankBounded (r : α→ℕ) : RankBounded r (rankZeta r) := by
  intro a b hab
  change (IncidenceAlgebra.zeta (Polynomial ℤ) a b*X^(r b-r a)).natDegree≤_
  rw [zeta_of_le hab,one_mul,natDegree_X_pow]

omit [LocallyFiniteOrder α] [DecidableEq α] in
@[simp] theorem barKernel_rankZeta (r : α→ℕ) : barKernel r (rankZeta r)=IncidenceAlgebra.zeta _ := by
  apply IncidenceAlgebra.ext
  intro a b hab
  change reflect (r b-r a) (IncidenceAlgebra.zeta (Polynomial ℤ) a b*X^(r b-r a))=_
  rw [zeta_of_le hab,one_mul]
  rw [← one_mul (X^(r b-r a)),← C_1,reflect_C_mul_X_pow]
  simp

theorem barKernel_zKernel (r : α→ℕ) (hr : Monotone r) : barKernel r (zKernel r)=zKernel r := by
  rw [zKernel,barKernel_mul r hr _ _ (rankZeta_rankBounded r) (klKernel_rankBounded r),
    barKernel_rankZeta,barKernel_kl r hr]
  rw [← mul_assoc,← mul_assoc,zeta_mul_constantMu,one_mul]

end MatroidInverseZ
