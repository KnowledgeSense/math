import SphericalTreeFailures.DensityConvolution

/-! # Affine scaling of the Fourier density -/
namespace SphericalTreeFailures
open MeasureTheory
open scoped ENNReal FourierTransform

theorem characteristicDensity_map_mul (μ : Measure ℝ) {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    characteristicDensity (μ.map (c * ·)) x = |c⁻¹| * characteristicDensity μ (x / c) := by
  have hcomplex : complexFourierIntegral (charFun (μ.map (c * ·))) 0 x =
      ((|c⁻¹| : ℝ) : ℂ) * complexFourierIntegral (charFun μ) 0 ((x / c : ℝ) : ℂ) := by
    unfold complexFourierIntegral
    simp only [pow_zero, one_mul, charFun_map_mul]
    let H : ℝ → ℂ := fun u => inverseFourierKernel u ((x / c : ℝ) : ℂ) * charFun μ u
    have he (t : ℝ) : inverseFourierKernel t (x : ℂ) * charFun μ (c * t) = H (c * t) := by
      dsimp [H]
      congr 1
      unfold inverseFourierKernel
      congr 1
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      push_cast
      field_simp
    simp_rw [he]
    rw [Measure.integral_comp_mul_left, Complex.real_smul]
    dsimp [H]
    ring
  have hre := congrArg Complex.re hcomplex
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  simpa only [← realFourierIntegral_zero_eq, realFourierIntegral] using hre

theorem charFun_map_mul_integrable (μ : Measure ℝ) (hint : Integrable (charFun μ))
    {c : ℝ} (hc : c ≠ 0) : Integrable (charFun (μ.map (c * ·))) := by
  have he : charFun (μ.map (c * ·)) = fun t => charFun μ (c * t) := funext (charFun_map_mul c)
  rw [he]
  exact hint.comp_mul_left' hc

end SphericalTreeFailures
