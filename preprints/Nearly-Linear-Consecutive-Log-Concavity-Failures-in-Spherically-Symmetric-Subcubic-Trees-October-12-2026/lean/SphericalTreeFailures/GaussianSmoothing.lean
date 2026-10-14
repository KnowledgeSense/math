import SphericalTreeFailures.EntireFourierIntegral
import Mathlib.Analysis.Fourier.Inversion

/-! # Gaussian regularization of an actual characteristic function -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology ENNReal FourierTransform

noncomputable def gaussianFrequency (a t : ℝ) : ℂ :=
  Complex.exp ((-Real.pi * a * t ^ 2 : ℝ) : ℂ)

noncomputable def gaussianSpatial (a x : ℝ) : ℝ :=
  (Real.sqrt a)⁻¹ * Real.exp (-Real.pi / a * x ^ 2)

theorem gaussianFrequency_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussianFrequency a) := by
  have h := (integrable_exp_neg_mul_sq (mul_pos Real.pi_pos ha)).ofReal (𝕜 := ℂ)
  unfold gaussianFrequency
  simpa [Complex.ofReal_exp, mul_assoc] using h

theorem gaussianFrequency_fourier {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (gaussianFrequency a) x = (gaussianSpatial a x : ℂ) := by
  have he : gaussianFrequency a = fun t : ℝ =>
      Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (t : ℂ) ^ 2) := by
    funext t
    simp [gaussianFrequency]
  rw [he, fourier_gaussian_pi (by simpa : 0 < (a : ℂ).re)]
  have hs : (a : ℂ) ^ (2⁻¹ : ℂ) = (Real.sqrt a : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  simp only [hs, gaussianSpatial, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, one_div]

theorem gaussianSpatial_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ gaussianSpatial a x := by
  unfold gaussianSpatial
  positivity

theorem gaussianSpatial_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussianSpatial a) := by
  unfold gaussianSpatial
  simpa only [neg_div] using (integrable_exp_neg_mul_sq (div_pos Real.pi_pos ha)).const_mul (Real.sqrt a)⁻¹

theorem gaussianSpatial_integral {a : ℝ} (ha : 0 < a) : ∫ x, gaussianSpatial a x = 1 := by
  unfold gaussianSpatial
  simp_rw [neg_div]
  rw [integral_const_mul, integral_gaussian]
  have he : Real.pi / (Real.pi / a) = a := by field_simp
  rw [he, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ha))]

noncomputable def smoothedCharacteristic (μ : Measure ℝ) (a t : ℝ) : ℂ :=
  charFun μ t * gaussianFrequency a t

noncomputable def gaussianSmoothing (μ : Measure ℝ) (a x : ℝ) : ℝ :=
  ∫ y, gaussianSpatial a (x - y / (2 * Real.pi)) ∂μ

theorem gaussianSmoothing_nonneg (μ : Measure ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ gaussianSmoothing μ a x := integral_nonneg fun _y => gaussianSpatial_nonneg ha _

theorem gaussianSmoothing_integrable_prod (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ × ℝ => gaussianSpatial a (z.1 - z.2 / (2 * Real.pi)))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => gaussianSpatial a (z.1 - z.2 / (2 * Real.pi))) (volume.prod μ) :=
    (show Continuous (fun z : ℝ × ℝ => gaussianSpatial a (z.1 - z.2 / (2 * Real.pi))) by
      unfold gaussianSpatial; fun_prop).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply ae_of_all
    intro y
    change Integrable (fun x : ℝ => gaussianSpatial a (x - y / (2 * Real.pi))) volume
    exact (gaussianSpatial_integrable ha).comp_sub_right (y / (2 * Real.pi))
  · have he (y : ℝ) : (∫ x : ℝ, ‖gaussianSpatial a (x - y / (2 * Real.pi))‖) = 1 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (gaussianSpatial_nonneg ha _)]
      rw [integral_sub_right_eq_self, gaussianSpatial_integral ha]
    simp_rw [he]
    exact integrable_const _

theorem gaussianSmoothing_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) : Integrable (gaussianSmoothing μ a) :=
  (gaussianSmoothing_integrable_prod μ ha).integral_prod_left

theorem gaussianSmoothing_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) : ∫ x, gaussianSmoothing μ a x = 1 := by
  unfold gaussianSmoothing
  rw [integral_integral_swap (gaussianSmoothing_integrable_prod μ ha)]
  simp_rw [integral_sub_right_eq_self, gaussianSpatial_integral ha]
  simp

noncomputable def gaussianFourierIntegrand (a x t y : ℝ) : ℂ :=
  Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) *
    Complex.exp ((t : ℂ) * y * Complex.I) * gaussianFrequency a t

theorem gaussianFourierIntegrand_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (Function.uncurry (gaussianFourierIntegrand a x)) (volume.prod μ) := by
  have hm : AEStronglyMeasurable (Function.uncurry (gaussianFourierIntegrand a x)) (volume.prod μ) :=
    (show Continuous (Function.uncurry (gaussianFourierIntegrand a x)) by
      change Continuous (fun z : ℝ × ℝ =>
        Complex.exp ((-2 * Real.pi * z.1 * x : ℝ) * Complex.I) *
          Complex.exp ((z.1 : ℂ) * z.2 * Complex.I) *
          Complex.exp ((-Real.pi * a * z.1 ^ 2 : ℝ) : ℂ))
      fun_prop).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply ae_of_all
    intro t
    change Integrable (gaussianFourierIntegrand a x t) μ
    exact ((integrable_probability_exponential μ t).const_mul
      (Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I))).mul_const (gaussianFrequency a t)
  · change Integrable (fun t : ℝ => ∫ y, ‖gaussianFourierIntegrand a x t y‖ ∂μ) volume
    have he (t : ℝ) :
        (∫ y, ‖gaussianFourierIntegrand a x t y‖ ∂μ) = ‖gaussianFrequency a t‖ := by
      simp [gaussianFourierIntegrand, Complex.norm_exp]
    simp_rw [he]
    exact (gaussianFrequency_integrable ha).norm

theorem smoothedCharacteristic_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (smoothedCharacteristic μ a) x = (gaussianSmoothing μ a x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (t : ℝ) :
      Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) • smoothedCharacteristic μ a t =
        ∫ y, gaussianFourierIntegrand a x t y ∂μ := by
    simp only [gaussianFourierIntegrand, integral_mul_const, integral_const_mul,
      smoothedCharacteristic, charFun_apply_real, smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_integral_swap (gaussianFourierIntegrand_integrable μ ha x)]
  have hinner (y : ℝ) : (∫ t, gaussianFourierIntegrand a x t y) =
      (gaussianSpatial a (x - y / (2 * Real.pi)) : ℂ) := by
    rw [← gaussianFrequency_fourier ha, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    dsimp [gaussianFourierIntegrand]
    rw [← Complex.exp_add]
    congr 2
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  simp_rw [hinner]
  rw [integral_complex_ofReal]
  rfl

end SphericalTreeFailures
