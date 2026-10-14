import AperyMoments.SpectralFubini
import AperyMoments.LatticeShiftMoments

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace AperyMoments

theorem spectralPower_integrable {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    Integrable (fun w : ℝ => w ^ n * spectralDensity b w) := by
  have hi := spectralTest_integrable hb (show Continuous (fun w : ℝ => ((w ^ n : ℝ) : ℂ)) by fun_prop)
    (show ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖((w ^ n : ℝ) : ℂ)‖ ≤ (4 + b) ^ n by
      intro w hw
      rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg w) (abs_le.mpr hw) n)
  have hr := hi.re
  change Integrable (fun w : ℝ => (((w ^ n : ℝ) : ℂ) * (spectralDensity b w : ℂ)).re) at hr
  simpa only [← Complex.ofReal_mul, Complex.ofReal_re] using hr

theorem spectralMoment_even {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    (∫ w : ℝ, w ^ (2 * n) * spectralDensity b w) =
      ∑ j ∈ Finset.range (n + 1), ((2 * n).choose (2 * j) : ℝ) * (j.centralBinom : ℝ) ^ 2 *
        (b ^ 2 / 4) ^ (n - j) * ((n - j).centralBinom : ℝ) := by
  have h := spectralTest_integral_real hb (show Continuous (fun w : ℝ => w ^ (2 * n)) by fun_prop)
    (show ∀ w ∈ Icc (-(4 + b)) (4 + b), |w ^ (2 * n)| ≤ (4 + b) ^ (2 * n) by
      intro w hw
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg w) (abs_le.mpr hw) (2 * n))
  rw [h]
  simp_rw [latticeShift_even_moment]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun θ : ℝ => ((2 * n).choose (2 * j) : ℝ) *
        (b * Real.cos θ) ^ (2 * (n - j)) * (j.centralBinom : ℝ) ^ 2) =
        (fun θ => (((2 * n).choose (2 * j) : ℝ) * b ^ (2 * (n - j)) * (j.centralBinom : ℝ) ^ 2) *
          Real.cos θ ^ (2 * (n - j))) := by funext θ; rw [mul_pow]; ring
    rw [he, intervalIntegral.integral_const_mul, cosineMoment_even, div_pow, pow_mul]
    field_simp
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

theorem spectralMoment_odd {b : ℝ} (_hb : 0 ≤ b) (n : ℕ) :
    (∫ w : ℝ, w ^ (2 * n + 1) * spectralDensity b w) = 0 := by
  have h := integral_neg_eq_self (μ := volume) (fun w : ℝ => w ^ (2 * n + 1) * spectralDensity b w)
  have he : (fun w : ℝ => (-w) ^ (2 * n + 1) * spectralDensity b (-w)) =
      (fun w => -(w ^ (2 * n + 1) * spectralDensity b w)) := by
    funext w
    rw [spectralDensity_neg]
    simp [pow_add, pow_mul]
  rw [he, integral_neg] at h
  linarith

theorem spectralMoment_reciprocal_parameter {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    (∫ w : ℝ, w ^ (2 * n) * spectralDensity (2 * Real.sqrt α) w) =
      ∑ j ∈ Finset.range (n + 1), ((2 * n).choose (2 * j) : ℝ) * (j.centralBinom : ℝ) ^ 2 *
        α ^ (n - j) * ((n - j).centralBinom : ℝ) := by
  rw [spectralMoment_even (by positivity)]
  have he : (2 * Real.sqrt α) ^ 2 / 4 = α := by rw [mul_pow, Real.sq_sqrt hα]; ring
  rw [he]

end AperyMoments
