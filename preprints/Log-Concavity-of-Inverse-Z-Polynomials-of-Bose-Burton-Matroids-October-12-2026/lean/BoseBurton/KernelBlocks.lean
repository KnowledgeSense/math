import BoseBurton.KernelCoefficients
import BoseBurton.OrientationSums
import BoseBurton.KernelExponentAlgebra

noncomputable section
namespace BoseBurton
open Finset Polynomial

def kernelBlock (z : ℝ) (r s h : ℕ) : Polynomial ℝ :=
  ∑ l∈range (min h (r-h)+1),
    C ((-1:ℝ)^(h+l)*z^(h*(r-s)+h.choose 2+l.choose 2)*
      gaussian z s h*gaussian z (r-h) l)*
    orientationPolynomial h l*gaussianRow z (r-h-l)

def upperPartialTerm (z : ℝ) (r s h k : ℕ) : ℝ :=
  if h<k ∧ k≤r-h then z^(h*(r-s+h))*gaussian z s h*
    gaussian z (r-h) k*gaussian z (k-1) h else 0

def lowerPartialTerm (z : ℝ) (r s h k : ℕ) : ℝ :=
  if h≤k ∧ h≤r-k then z^(h*(r-s+h-1))*gaussian z s h*
    gaussian z (r-h) (k-h)*gaussian z (r-k-1) (h-1) else 0

theorem kernelBlock_coeff_orientations (z : ℝ) (r s h k : ℕ) :
    (kernelBlock z r s h).coeff k=
      ((-1:ℝ)^h*z^(h*(r-s)+h.choose 2)*gaussian z s h)*
      ((∑ l∈range (min h (r-h)+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z (r-h) l*
        (if l≤k then gaussian z (r-h-l) (k-l) else 0))+
       if h≤k then
         ∑ l∈range (min h (r-h)+1),(-1:ℝ)^l*z^(l.choose 2)*gaussian z (r-h) l*
           (if l<h then gaussian z (r-h-l) (k-h) else 0)
       else 0) := by
  unfold kernelBlock
  rw [finsetSum_coeff]
  by_cases hhk : h≤k
  · rw [ite_eq_left hhk,← sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro l hl
    have hlh : l≤h := by simp only [mem_range] at hl; omega
    rw [mul_assoc,coeff_C_mul,orientation_gaussianRow_coeff z (r-h-l) h l k hlh]
    simp only [hhk,and_true,pow_add]
    ring
  · rw [ite_eq_right hhk,add_zero,mul_sum]
    apply sum_congr rfl
    intro l hl
    have hlh : l≤h := by simp only [mem_range] at hl; omega
    rw [mul_assoc,coeff_C_mul,orientation_gaussianRow_coeff z (r-h-l) h l k hlh]
    simp only [hhk,and_false,ite_false,add_zero,pow_add]
    ring

end BoseBurton
