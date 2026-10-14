import BoseBurton.KernelInternal
import BoseBurton.KernelSymmetry
import BoseBurton.GaussianProduct

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem kernelBlock_coeff_zero (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s h : ℕ) (hh : 1≤h) :
    (kernelBlock z r s h).coeff 0=gaussianTerm z (z^(r-s)) s h := by
  rw [kernelBlock_coeff_orientations]
  simp only [show ¬h≤0 by omega,ite_false,add_zero,Nat.le_zero_eq]
  simp only [mul_ite,mul_zero]
  rw [sum_ite_eq']
  simp only [mem_range,show 0<min h (r-h)+1 by omega,ite_true,
    pow_zero,Nat.choose_zero_succ,zero_tsub,Nat.sub_zero,mul_one,
    gaussian_zero_right z hz0 hz1]
  unfold gaussianTerm
  rw [pow_add,← pow_mul,show (r-s)*h=h*(r-s) by ring]
  ring

theorem signedKernel_coeff_zero (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s : ℕ) : (signedKernel z r s).coeff 0=endpointFactor z r s := by
  rw [signedKernel_eq_blocks,coeff_add,gaussianRow_coeff,gaussian_zero_right z hz0 hz1,finsetSum_coeff]
  have he : (∑ h∈Icc 1 s,(kernelBlock z r s h).coeff 0)=
      ∑ h∈Icc 1 s,gaussianTerm z (z^(r-s)) s h := by
    apply sum_congr rfl
    intro h hh
    exact kernelBlock_coeff_zero z hz0 hz1 r s h (mem_Icc.mp hh).1
  rw [he,sum_Icc_one_eq_range]
  have hp := gaussian_product z (z^(r-s)) hz0 hz1 s
  change (∑ h∈range (s+1),gaussianTerm z (z^(r-s)) s h)=_ at hp
  rw [sum_range_succ',gaussianTerm_zero z (z^(r-s)) hz0 hz1] at hp
  rw [add_comm, hp]
  unfold endpointFactor
  apply prod_congr rfl
  intro i _
  rw [← pow_add]

theorem signedKernel_coeff_symm (z : ℝ) (r s k : ℕ) (hsr : s≤r) (hk : k≤r) :
    (signedKernel z r s).coeff (r-k)=(signedKernel z r s).coeff k := by
  rw [signedKernel_eq_blocks,coeff_add,coeff_add,gaussianRow_coeff,gaussianRow_coeff,
    gaussian_symm z r k hk,finsetSum_coeff,finsetSum_coeff]
  congr 1
  apply sum_congr rfl
  intro h hh
  exact kernelBlock_coeff_symm z r s h k (by have := (mem_Icc.mp hh).2; omega) hk

end BoseBurton
