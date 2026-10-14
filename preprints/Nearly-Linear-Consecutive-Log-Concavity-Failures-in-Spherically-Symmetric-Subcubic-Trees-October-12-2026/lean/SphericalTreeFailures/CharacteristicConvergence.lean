import SphericalTreeFailures.GraphSizeDistribution
import SphericalTreeFailures.RootTotalLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal

 theorem sizeExponential_sub_norm_le (x y t : ℝ) :
    ‖sizeExponential x t - sizeExponential y t‖ ≤ |t| * |x - y| := by
  have he : sizeExponential x t - sizeExponential y t =
      (sizeExponential (x - y) t - 1) * sizeExponential y t := by
    rw [sub_mul, one_mul, ← sizeExponential_add]
    rw [sub_add_cancel]
  rw [he, norm_mul, sizeExponential_norm, mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * (x - y))
  have he' : Complex.I * ((t * (x - y) : ℝ) : ℂ) = ((x - y : ℝ) : ℂ) * ((t : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he'] at h
  simpa only [sizeExponential, Real.norm_eq_abs, abs_mul] using h

theorem integral_abs_le_L2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ∫ ω, |f ω| ∂μ ≤ (eLpNorm f 2 μ).toReal := by
  simp_rw [← Real.norm_eq_abs]
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

theorem characteristic_difference_L2_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : MemLp (f - g) 2 μ) (t : ℝ) :
    ‖(∫ ω, sizeExponential (f ω) t ∂μ) - ∫ ω, sizeExponential (g ω) t ∂μ‖ ≤
      |t| * (eLpNorm (f - g) 2 μ).toReal := by
  rw [← integral_sub (integrable_sizeExponential μ hf t) (integrable_sizeExponential μ hg t)]
  calc
    _ ≤ ∫ ω, |t| * |f ω - g ω| ∂μ := norm_integral_le_of_norm_le
      ((hfg.integrable (by norm_num)).norm.const_mul |t|)
      (Filter.Eventually.of_forall fun ω => sizeExponential_sub_norm_le _ _ _)
    _ = |t| * ∫ ω, |(f - g) ω| ∂μ := by rw [integral_const_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_L2 μ hfg) (abs_nonneg _)

end SphericalTreeFailures
