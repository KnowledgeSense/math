import BoseBurton.ZIncidenceConvolution

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

theorem z_inverseZ_signed_convolution (r : α→ℕ) (hr : Monotone r) (a b : α) (hab : a<b) :
    (∑ x∈Icc a b,C ((-1:ℤ)^(r x-r a))*zKernel r a x*inverseZ r x b)=0 := by
  have hc := z_inverseZ_convolution r hr a b
  rw [ite_eq_right hab.ne] at hc
  calc
    _ = C ((-1:ℤ)^(r b-r a))*(∑ x∈Icc a b,
        zKernel r a x*(C ((-1:ℤ)^(r b-r x))*inverseZ r x b)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hra := hr (mem_Icc.mp hx).1
      have hrb := hr (mem_Icc.mp hx).2
      have he : r b-r a=(r x-r a)+(r b-r x) := by omega
      have hs : (-1:ℤ)^(r b-r a)*(-1)^(r b-r x)=(-1)^(r x-r a) := by
        rw [he,pow_add,mul_assoc,← mul_pow]
        norm_num
      calc
        _ = (C ((-1:ℤ)^(r b-r a))*C ((-1:ℤ)^(r b-r x)))*zKernel r a x*inverseZ r x b := by
          rw [← map_mul,hs]
        _ = _ := by ring
    _ = 0 := by rw [hc,mul_zero]

theorem inverseZ_from_zKernel (r : α→ℕ) (hr : Monotone r) (a b : α) (hab : a<b) :
    inverseZ r a b=-(∑ x∈Ioc a b,C ((-1:ℤ)^(r x-r a))*zKernel r a x*inverseZ r x b) := by
  have h := z_inverseZ_signed_convolution r hr a b hab
  rw [Icc_eq_cons_Ioc hab.le,sum_cons] at h
  simp only [Nat.sub_self,pow_zero,map_one,one_mul,zKernel_diag] at h
  exact eq_neg_of_add_eq_zero_left h

end MatroidInverseZ
