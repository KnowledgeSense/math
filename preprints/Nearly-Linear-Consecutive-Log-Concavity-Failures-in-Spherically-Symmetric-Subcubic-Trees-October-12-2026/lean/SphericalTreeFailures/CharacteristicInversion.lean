import SphericalTreeFailures.CharacteristicDensity

/-! # Density identification from an integrable characteristic function -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform

noncomputable def characteristicDensity (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (𝓕 (charFun μ) (x / (2 * Real.pi))).re

theorem characteristicDensity_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) : 0 ≤ characteristicDensity μ x :=
  mul_nonneg (by positivity) (charFun_fourier_nonnegative_real μ hint _).1

theorem characteristicDensity_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) : Integrable (characteristicDensity μ) := by
  have h := (charFun_fourier_real_integrable μ hint).comp_mul_right'
    (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  unfold characteristicDensity
  simpa only [div_eq_mul_inv] using h.const_mul (2 * Real.pi)⁻¹

theorem charFun_fourier_continuous (μ : Measure ℝ) (hint : Integrable (charFun μ)) :
    Continuous (𝓕 (charFun μ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hint

theorem characteristicDensity_continuous (μ : Measure ℝ) (hint : Integrable (charFun μ)) :
    Continuous (characteristicDensity μ) :=
  continuous_const.mul (Complex.continuous_re.comp
    ((charFun_fourier_continuous μ hint).comp (continuous_id.div_const _)))

theorem complexFourierIntegral_zero_eq (φ : ℝ → ℂ) (x : ℝ) :
    complexFourierIntegral φ 0 x = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * 𝓕 φ (x / (2 * Real.pi)) := by
  unfold complexFourierIntegral
  simp only [pow_zero, one_mul]
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  simp only [smul_eq_mul]
  congr 1
  unfold inverseFourierKernel
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem realFourierIntegral_zero_eq (μ : Measure ℝ) (x : ℝ) :
    realFourierIntegral (charFun μ) 0 x = characteristicDensity μ x := by
  rw [realFourierIntegral, complexFourierIntegral_zero_eq]
  simp [characteristicDensity]

theorem charFun_fourier_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) (x : ℝ) :
    ((𝓕 (charFun μ) x).re : ℂ) = 𝓕 (charFun μ) x := by
  apply Complex.ext
  · simp
  · simp [(charFun_fourier_nonnegative_real μ hint x).2]

/-- An integrable characteristic function determines its genuine Lebesgue density. -/
theorem measure_eq_withDensity_characteristicDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (charFun μ)) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (characteristicDensity μ x)) := by
  let f := characteristicDensity μ
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hf : Integrable f := characteristicDensity_integrable μ hint
  have hfn (x : ℝ) : 0 ≤ f x := characteristicDensity_nonneg μ hint x
  have hfm : Measurable f := (characteristicDensity_continuous μ hint).measurable
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  apply Measure.ext_of_charFun
  funext t
  symm
  change charFun ν t = charFun μ t
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
  simp only [ENNReal.toReal_ofReal (hfn _), Complex.real_smul]
  have hfe (x : ℝ) : (f x : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      𝓕 (charFun μ) (x / (2 * Real.pi)) := by
    dsimp [f, characteristicDensity]
    rw [Complex.ofReal_mul, Complex.ofReal_inv, charFun_fourier_eq_real μ hint]
  simp_rw [hfe]
  let H : ℝ → ℂ := fun y => Complex.exp ((t : ℂ) * (((2 * Real.pi) * y : ℝ) : ℂ) * Complex.I) *
    𝓕 (charFun μ) y
  have he (x : ℝ) :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * 𝓕 (charFun μ) (x / (2 * Real.pi))) *
        Complex.exp ((t : ℂ) * x * Complex.I) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * H ((2 * Real.pi)⁻¹ * x) := by
    dsimp [H]
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hx : (2 * Real.pi) * ((2 * Real.pi)⁻¹ * x) = x := by field_simp
    rw [hx, div_eq_mul_inv, mul_comm (2 * Real.pi)⁻¹ x]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [inv_inv, abs_of_pos hp, Complex.real_smul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hp)), one_mul]
  have hi : (∫ y, H y) = 𝓕⁻ (𝓕 (charFun μ)) t := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    apply ae_of_all
    intro y
    dsimp [H]
    congr 1
    congr 1
    simp only [starRingEnd_apply, star_trivial]
    push_cast
    ring
  rw [hi]
  exact hint.fourierInv_fourier_eq (charFun_fourier_integrable μ hint) continuous_charFun.continuousAt

end SphericalTreeFailures
