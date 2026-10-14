import BoseBurton.SignedKernel
import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem gaussianRow_coeff (z : ℝ) (n k : ℕ) : (gaussianRow z n).coeff k=gaussian z n k := by
  classical
  simp only [gaussianRow,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  by_cases hk : k≤n
  · simp [show k<n+1 by omega]
  · simp [show ¬k<n+1 by omega,gaussian, hk]

theorem orientationPolynomial_eq (h l : ℕ) (hl : l≤h) :
    orientationPolynomial h l=X^l+(if l<h then X^h else 0) := by
  by_cases he : l<h
  · simp [orientationPolynomial,he]
  · have heq : l=h := by omega
    simp [orientationPolynomial,heq]

theorem orientation_gaussianRow_coeff (z : ℝ) (n h l k : ℕ) (hl : l≤h) :
    (orientationPolynomial h l*gaussianRow z n).coeff k=
      (if l≤k then gaussian z n (k-l) else 0)+
      (if l<h ∧ h≤k then gaussian z n (k-h) else 0) := by
  rw [orientationPolynomial_eq h l hl,add_mul,coeff_add]
  by_cases hlk : l≤k <;> by_cases hlh : l<h <;> by_cases hhk : h≤k <;>
    simp [hlk,hlh,hhk,coeff_X_pow_mul',gaussianRow_coeff]

end BoseBurton
