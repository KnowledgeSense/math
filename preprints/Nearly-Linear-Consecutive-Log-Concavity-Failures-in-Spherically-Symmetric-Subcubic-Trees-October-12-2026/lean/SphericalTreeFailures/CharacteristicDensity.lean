import SphericalTreeFailures.GaussianSmoothing

/-! # Integrability and positivity in characteristic-function inversion -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal FourierTransform

theorem gaussianFrequency_tendsto_zero_parameter (t : ℝ) :
    Tendsto (fun n : ℕ => gaussianFrequency (1 / ((n : ℝ) + 1)) t) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => -Real.pi * (1 / ((n : ℝ) + 1)) * t ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-Real.pi)).mul_const (t ^ 2)
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (Complex.continuous_ofReal.continuousAt.tendsto.comp h)
  simpa only [Function.comp_def, gaussianFrequency, Complex.ofReal_zero, Complex.exp_zero] using he

theorem fourier_smoothedCharacteristic_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    Tendsto (fun n : ℕ => 𝓕 (smoothedCharacteristic μ (1 / ((n : ℝ) + 1))) x)
      atTop (𝓝 (𝓕 (charFun μ) x)) := by
  simp only [Real.fourier_real_eq_integral_exp_smul]
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖charFun μ t‖)
  · intro n
    have hχ := continuous_charFun (μ := μ)
    exact (show Continuous (fun t : ℝ =>
      Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) •
        smoothedCharacteristic μ (1 / ((n : ℝ) + 1)) t) by
      unfold smoothedCharacteristic gaussianFrequency; fun_prop).aestronglyMeasurable
  · exact hint.norm
  · intro n
    apply ae_of_all
    intro t
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hg : ‖gaussianFrequency (1 / ((n : ℝ) + 1)) t‖ ≤ 1 := by
      simp only [gaussianFrequency, Complex.norm_exp, Complex.ofReal_re]
      apply Real.exp_le_one_iff.mpr
      have hh := mul_nonneg (mul_nonneg Real.pi_pos.le hn.le) (sq_nonneg t)
      nlinarith
    simp only [smoothedCharacteristic, norm_smul, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, zero_mul, sub_self,
      Real.exp_zero, one_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hg
  · apply ae_of_all
    intro t
    have hh := (tendsto_const_nhds (x := charFun μ t)).mul
      (gaussianFrequency_tendsto_zero_parameter t)
    have hh' := hh.const_smul (Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I))
    simpa only [mul_one, smoothedCharacteristic] using hh'

theorem gaussianSmoothing_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    Tendsto (fun n : ℕ => gaussianSmoothing μ (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 (𝓕 (charFun μ) x).re) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (fourier_smoothedCharacteristic_tendsto μ hint x)
  have he (n : ℕ) : (𝓕 (smoothedCharacteristic μ (1 / ((n : ℝ) + 1))) x).re =
      gaussianSmoothing μ (1 / ((n : ℝ) + 1)) x := by
    rw [smoothedCharacteristic_fourier μ (by positivity)]
    simp
  simpa only [Function.comp_def, he] using h

theorem charFun_fourier_nonnegative_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    0 ≤ (𝓕 (charFun μ) x).re ∧ (𝓕 (charFun μ) x).im = 0 := by
  constructor
  · exact ge_of_tendsto (gaussianSmoothing_tendsto μ hint x)
      (Eventually.of_forall fun n : ℕ => gaussianSmoothing_nonneg μ
        (a := 1 / ((n : ℝ) + 1)) (by positivity) x)
  · have h := Complex.continuous_im.continuousAt.tendsto.comp
      (fourier_smoothedCharacteristic_tendsto μ hint x)
    have he (n : ℕ) : (𝓕 (smoothedCharacteristic μ (1 / ((n : ℝ) + 1))) x).im = 0 := by
      rw [smoothedCharacteristic_fourier μ (by positivity)]
      simp
    simp only [Function.comp_def, he] at h
    exact tendsto_nhds_unique h tendsto_const_nhds

theorem charFun_fourier_real_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) : Integrable (fun x : ℝ => (𝓕 (charFun μ) x).re) := by
  let G : ℕ → ℝ → ℝ := fun n => gaussianSmoothing μ (1 / ((n : ℝ) + 1))
  have hG (n : ℕ) : Integrable (G n) := gaussianSmoothing_integrable μ (by positivity)
  have he (n : ℕ) : (∫⁻ x, ‖G n x‖ₑ) = 1 := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hG n)]
    have hz (x : ℝ) : ‖G n x‖ = G n x := Real.norm_of_nonneg (gaussianSmoothing_nonneg μ (by positivity) x)
    simp_rw [hz]
    rw [gaussianSmoothing_integral μ (by positivity), ENNReal.ofReal_one]
  apply integrable_of_tendsto (ae_of_all _ (gaussianSmoothing_tendsto μ hint))
    (fun n => (hG n).aestronglyMeasurable)
  change liminf (fun n : ℕ => ∫⁻ x, ‖G n x‖ₑ) atTop ≠ ⊤
  simp only [he, liminf_const, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

theorem charFun_fourier_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) : Integrable (𝓕 (charFun μ)) := by
  have he : 𝓕 (charFun μ) = fun x : ℝ => ((𝓕 (charFun μ) x).re : ℂ) := by
    funext x
    apply Complex.ext
    · simp
    · simp [ (charFun_fourier_nonnegative_real μ hint x).2]
  rw [he]
  exact (charFun_fourier_real_integrable μ hint).ofReal

end SphericalTreeFailures
