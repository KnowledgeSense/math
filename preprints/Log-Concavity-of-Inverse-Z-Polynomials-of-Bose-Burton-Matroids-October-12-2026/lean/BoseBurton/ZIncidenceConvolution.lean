import BoseBurton.ZIncidence

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

theorem zKernel_reflect (r : α→ℕ) (hr : Monotone r) (a b : α) :
    reflect (r b-r a) (zKernel r a b)=zKernel r a b := by
  exact congrArg (fun f : IncidenceAlgebra (Polynomial ℤ) α=>f a b) (barKernel_zKernel r hr)

theorem zKernel_coeff_symm (r : α→ℕ) (hr : Monotone r) (a b : α)
    (k : ℕ) (hk : k≤r b-r a) :
    (zKernel r a b).coeff k=(zKernel r a b).coeff (r b-r a-k) := by
  have h := congrArg (fun p : Polynomial ℤ=>p.coeff k) (zKernel_reflect r hr a b)
  simpa only [coeff_reflect,revAt_le hk] using h.symm

omit [DecidableLE α] in
theorem signedInverseZKernel_apply (r : α→ℕ) (hr : Monotone r) (a b : α) :
    signedInverseZKernel r a b=C ((-1:ℤ)^(r b-r a))*inverseZ r a b := by
  rw [inverseZ_eq_signed_product r hr]
  change _=C ((-1:ℤ)^(r b-r a))*(C ((-1:ℤ)^(r b-r a))*signedInverseZKernel r a b)
  rw [← mul_assoc,← map_mul,← mul_pow]
  norm_num

theorem z_inverseZ_convolution (r : α→ℕ) (hr : Monotone r) (a b : α) :
    (∑ x∈Icc a b,zKernel r a x*(C ((-1:ℤ)^(r b-r x))*inverseZ r x b))=
      if a=b then 1 else 0 := by
  have h := congrArg (fun f : IncidenceAlgebra (Polynomial ℤ) α=>f a b)
    (zKernel_mul_signedInverseZKernel r hr)
  simpa only [mul_apply,signedInverseZKernel_apply r hr,one_apply] using h

end MatroidInverseZ
