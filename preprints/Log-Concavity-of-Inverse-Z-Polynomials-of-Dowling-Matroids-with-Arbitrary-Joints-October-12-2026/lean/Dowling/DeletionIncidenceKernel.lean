import Dowling.DeletionKLTau

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ IncidenceAlgebra
open scoped Classical
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]

/-- Rank-normalized literal substitution on incidence kernels. -/
def deletionKernelLift (r : α→ℕ) (f : IncidenceAlgebra (Polynomial ℤ) α) :
    IncidenceAlgebra DeletionLaurent α where
  toFun a b := deletionLift ((r b : ℤ)-r a) (f a b)
  eq_zero_of_not_le' {_ _} h := by rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; simp [deletionLift]

 omit [LocallyFiniteOrder α] in
 theorem deletionKernelLift_apply (r : α→ℕ) (f : IncidenceAlgebra (Polynomial ℤ) α) (a b : α) :
    deletionKernelLift r f a b=deletionLift ((r b : ℤ)-r a) (f a b) := rfl

 theorem deletionKernelLift_mul (r : α→ℕ) (f g : IncidenceAlgebra (Polynomial ℤ) α) :
    deletionKernelLift r (f*g)=deletionKernelLift r f*deletionKernelLift r g := by
  apply IncidenceAlgebra.ext
  intro a b hab
  rw [deletionKernelLift_apply,mul_apply,deletionLift_finset_sum,mul_apply]
  apply sum_congr rfl
  intro x hx
  rw [deletionKernelLift_apply,deletionKernelLift_apply,← deletionLift_mul]
  congr 1
  ring

 theorem deletionKernelLift_kl (r : α→ℕ) (a b : α) :
    deletionKernelLift r (klKernel r) a b=deletionKLVector r b a := by
  by_cases hab : a≤b
  · simp [deletionKernelLift_apply,deletionKLVector,hab]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hab]
    simp [deletionKLVector,hab]

 theorem deletionKL_mul_signedY (r : α→ℕ) :
    klKernel r*signedInverseZKernel r=rankMu r := by
  rw [signedInverseZKernel,← mul_assoc,
    incidence_rightInverse_of_leftInverse _ _ (fun x=>kl_self r x) (klInverseKernel_mul_klKernel r),one_mul]

 theorem deletionKernelLift_rankMu (r : α→ℕ) (hr : Monotone r) (a b : α) (hab : a≤b) :
    deletionKernelLift r (rankMu r) a b=T ((r a : ℤ)-r b)*C (IncidenceAlgebra.mu ℤ a b) := by
  rw [deletionKernelLift_apply]
  simp only [rankMu,IncidenceAlgebra.coe_mk]
  rw [mul_comm,deletionLift_Xpow_mul,deletionSubst_C]
  congr 2
  have := hr hab
  omega

/-- Expansion of the actual Möbius vector in the KL basis, with literal signed inverse-Z coefficients. -/
theorem deletionMobiusVector_expansion (r : α→ℕ) (hr : Monotone r) (a t : α) (hat : a≤t) :
    T (r a)*C (IncidenceAlgebra.mu ℤ a t)=
      ∑ b∈Icc a t,deletionKLVector r b a*
        deletionLift (2*(r t : ℤ)-r b) (signedInverseZKernel r b t) := by
  have h := congrArg (fun f : IncidenceAlgebra DeletionLaurent α=>f a t)
    (congrArg (deletionKernelLift r) (deletionKL_mul_signedY r))
  rw [deletionKernelLift_mul,mul_apply,deletionKernelLift_rankMu r hr a t hat] at h
  have hmul := congrArg (fun z : DeletionLaurent=>T (r t)*z) h
  rw [mul_sum] at hmul
  have hright : T (r t)*(T ((r a : ℤ)-r t)*C (IncidenceAlgebra.mu ℤ a t))=
      T (r a)*C (IncidenceAlgebra.mu ℤ a t) := by
    rw [← mul_assoc,← T_add]
    congr 2
    ring
  rw [hright] at hmul
  rw [← hmul]
  apply sum_congr rfl
  intro b hb
  rw [deletionKernelLift_kl,deletionKernelLift_apply]
  rw [show T (r t)*(deletionKLVector r b a*deletionLift ((r t : ℤ)-r b) (signedInverseZKernel r b t))=
      deletionKLVector r b a*(T (r t)*deletionLift ((r t : ℤ)-r b) (signedInverseZKernel r b t)) by ring,
    deletionLift_shift]
  congr 2
  ring

end Dowling
