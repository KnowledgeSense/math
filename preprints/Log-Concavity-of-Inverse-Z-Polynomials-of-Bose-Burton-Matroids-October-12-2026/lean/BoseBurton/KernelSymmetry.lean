import BoseBurton.KernelCoefficients
import BoseBurton.KernelBlocks

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem shiftedGaussian_reflect (z : ℝ) (r h l k : ℕ) (hhl : h+l≤r) (hk : k≤r) :
    (if l≤r-k then gaussian z (r-h-l) (r-k-l) else 0)=
      if h≤k then gaussian z (r-h-l) (k-h) else 0 := by
  by_cases hl : l≤r-k <;> by_cases hh : h≤k
  · rw [ite_eq_left hl,ite_eq_left hh]
    have he : r-k-l=(r-h-l)-(k-h) := by omega
    rw [he,gaussian_symm z (r-h-l) (k-h) (by omega)]
  · simp [hl,hh,gaussian_outside z (r-h-l) (r-k-l) (by omega)]
  · simp [hl,hh,gaussian_outside z (r-h-l) (k-h) (by omega)]
  · simp [hl,hh]

theorem orientation_gaussianRow_symm (z : ℝ) (r h l k : ℕ)
    (hlh : l≤h) (hhl : h+l≤r) (hk : k≤r) :
    (orientationPolynomial h l*gaussianRow z (r-h-l)).coeff (r-k)=
      (orientationPolynomial h l*gaussianRow z (r-h-l)).coeff k := by
  rw [orientation_gaussianRow_coeff z (r-h-l) h l (r-k) hlh,
    orientation_gaussianRow_coeff z (r-h-l) h l k hlh,
    shiftedGaussian_reflect z r h l k hhl hk]
  by_cases hlt : l<h
  · simp only [hlt,true_and]
    have he := shiftedGaussian_reflect z r l h k (by omega) hk
    rw [show r-l-h=r-h-l by omega] at he
    rw [he]
    ring
  · have he : l=h := by omega
    subst l
    simp

theorem kernelBlock_coeff_symm (z : ℝ) (r s h k : ℕ) (hhr : h≤r) (hk : k≤r) :
    (kernelBlock z r s h).coeff (r-k)=(kernelBlock z r s h).coeff k := by
  simp only [kernelBlock,finsetSum_coeff]
  apply sum_congr rfl
  intro l hl
  have hh : l≤h := by simp only [mem_range] at hl; omega
  have hsum : h+l≤r := by simp only [mem_range] at hl; omega
  rw [mul_assoc,coeff_C_mul,mul_assoc,coeff_C_mul,
    orientation_gaussianRow_symm z r h l k hh hsum hk]
  ring

end BoseBurton
