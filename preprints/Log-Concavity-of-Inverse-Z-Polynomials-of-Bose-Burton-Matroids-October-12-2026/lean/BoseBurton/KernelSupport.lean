import BoseBurton.KernelEndpoints
import BoseBurton.NormalizedConcavity

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem kernelBlock_coeff_above (z : ℝ) (r s h k : ℕ) (hh : h≤r) (hk : r<k) :
    (kernelBlock z r s h).coeff k=0 := by
  rw [kernelBlock,finsetSum_coeff]
  apply sum_eq_zero
  intro l hl
  have hln : l≤r-h := by simp only [mem_range] at hl; omega
  have hlh : l≤h := by simp only [mem_range] at hl; omega
  rw [mul_assoc,coeff_C_mul,orientation_gaussianRow_coeff z (r-h-l) h l k hlh]
  simp [gaussian_outside z (r-h-l) (k-l) (by omega),
    gaussian_outside z (r-h-l) (k-h) (by omega)]

theorem signedKernel_coeff_above (z : ℝ) (r s k : ℕ) (hsr : s≤r) (hk : r<k) :
    (signedKernel z r s).coeff k=0 := by
  rw [signedKernel_eq_blocks,coeff_add,gaussianRow_coeff,gaussian_outside z r k hk,
    zero_add,finsetSum_coeff]
  apply sum_eq_zero
  intro h hh
  exact kernelBlock_coeff_above z r s h k (by have := (mem_Icc.mp hh).2; omega) hk

theorem signedKernel_coeff_eq (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) :
    (signedKernel z r s).coeff k=scalarCoefficient z r s k := by
  by_cases hk0 : k=0
  · subst k
    simp [signedKernel_coeff_zero z hz0 hz1,scalarCoefficient,normalizedCoefficient,
      gaussian_zero_right z hz0 hz1]
  · by_cases hkr : k=r
    · subst k
      have h := signedKernel_coeff_symm z r s 0 hsr.le (by omega)
      simp only [Nat.sub_zero] at h
      rw [h,signedKernel_coeff_zero z hz0 hz1]
      simp [scalarCoefficient,normalizedCoefficient,gaussian_self z hz0 hz1]
    · by_cases hk : k<r
      · exact signedKernel_coeff_internal z hz0 hz1 r s k hsr (by omega) hk
      · rw [signedKernel_coeff_above z r s k hsr.le (by omega),scalarCoefficient,
          gaussian_outside z r k (by omega),zero_mul]

theorem signedKernel_coeff_pos (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) (hk : k≤r) : 0<(signedKernel z r s).coeff k := by
  rw [signedKernel_coeff_eq z hz0.le hz1 r s k hsr]
  exact scalarCoefficient_pos z hz0 hz1 r s k hsr hk

theorem signedKernel_strict_log_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hs : 1≤s) (hk : 1≤k) (hkr : k<r) :
    (signedKernel z r s).coeff (k-1)*(signedKernel z r s).coeff (k+1)<
      ((signedKernel z r s).coeff k)^2 := by
  have hz1 : z<1 := by linarith
  simp only [signedKernel_coeff_eq z hz0.le hz1 r s _ hsr]
  exact scalarCoefficient_strict_log_concave z hz0 hzhalf r s k hsr hs hk hkr

end BoseBurton
