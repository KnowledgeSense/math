import SphericalTreeFailures.GraphSizeDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace SphericalTreeFailures
open MeasureTheory

 theorem integer_fourier_orthogonality (n : ℤ) :
    (∫ t : ℝ in -Real.pi..Real.pi, sizeExponential (n : ℝ) t) =
      if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [sizeExponential]
    ring
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hn h))]
    have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hf (t : ℝ) : sizeExponential (n : ℝ) t = Complex.exp (((n : ℂ) * Complex.I) * t) := by
      unfold sizeExponential
      push_cast
      congr 1
      ring
    simp_rw [hf]
    rw [integral_exp_mul_complex hc]
    have he : ((n : ℂ) * Complex.I) * Real.pi =
        ((n : ℂ) * Complex.I) * (-Real.pi) + (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.ofReal_neg, sub_self, zero_div]

theorem finite_fourier_inversion {V : Type*} [Fintype V] (w : V → ℝ) (N : V → ℤ) (j : ℤ) :
    (∫ t : ℝ in -Real.pi..Real.pi,
      sizeExponential (-j : ℝ) t * ∑ v, (w v : ℂ) * sizeExponential (N v : ℝ) t) =
        ((2 * Real.pi : ℝ) : ℂ) * ∑ v, if N v = j then (w v : ℂ) else 0 := by
  have he (v : V) (t : ℝ) :
      sizeExponential (-j : ℝ) t * ((w v : ℂ) * sizeExponential (N v : ℝ) t) =
        (w v : ℂ) * sizeExponential ((N v - j : ℤ) : ℝ) t := by
    rw [mul_left_comm, ← sizeExponential_add]
    congr 2
    push_cast
    ring
  simp_rw [Finset.mul_sum, he]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integer_fourier_orthogonality, sub_eq_zero]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : N v = j <;> simp [h, mul_comm]
  · intro v _
    exact (continuous_const.mul (by unfold sizeExponential; fun_prop)).intervalIntegrable _ _

end SphericalTreeFailures
