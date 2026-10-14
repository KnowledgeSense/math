import CircleKernel.UniformExponential
import CircleKernel.EigenvalueAsymptotic

noncomputable section
open Finset Polynomial
namespace CircleKernel

def spectralCorrection (n : ℕ) : ℝ := circleEigenvalue n-2*Real.log n-spectralConstant

theorem exponentPolynomial_eval_inverse (M n : ℕ) :
    ((exponentPolynomial M).map (Rat.castHom ℂ)).eval (1/(n : ℂ)) =
      ∑ j ∈ range M, (CircleResidues.sourceCoefficient (j+1) : ℂ)/(n : ℂ)^(j+1) := by
  rw [eval_map, exponentPolynomial, PowerSeries.eval₂_trunc_eq_sum_range, sum_range_succ']
  simp only [PowerSeries.coeff_mk, CircleResidues.sourceCoefficient_zero, map_zero,
    zero_div, add_zero, Rat.coe_castHom, one_div_pow, mul_one_div]

theorem spectralCorrection_decomposition (M n : ℕ) :
    (spectralCorrection n : ℂ) =
      ((exponentPolynomial M).map (Rat.castHom ℂ)).eval (1/(n : ℂ)) +
        (eigenvalueError M n : ℂ) := by
  rw [exponentPolynomial_eval_inverse]
  simp only [spectralCorrection, eigenvalueError]
  push_cast
  ring

theorem complex_exp_difference_bound (u v : ℂ) :
    ‖Complex.exp u-Complex.exp v‖ ≤ ‖u-v‖*Real.exp (‖v‖+‖u-v‖) := by
  have he : Complex.exp u-Complex.exp v = Complex.exp v*(Complex.exp (u-v)-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, show v+(u-v)=u by ring]
  rw [he, norm_mul, Real.exp_add]
  have hd := Complex.norm_exp_sub_sum_le_norm_mul_exp (u-v) 1
  simp only [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at hd
  calc
    ‖Complex.exp v‖*‖Complex.exp (u-v)-1‖ ≤
        Real.exp ‖v‖*(‖u-v‖*Real.exp ‖u-v‖) :=
      mul_le_mul (Complex.norm_exp_le_exp_norm v) hd (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

end CircleKernel
