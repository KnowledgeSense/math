import AperyMoments.ReciprocalMomentCoefficients
import AperyMoments.MeasureScaling
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
namespace AperyMoments
open Set MeasureTheory Filter
open scoped ENNReal

def reciprocalMomentMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun t=>ENNReal.ofReal (reciprocalMomentDensity α t))

theorem reciprocalMomentDensity_mass {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    (∫ t:ℝ,reciprocalMomentDensity α t)=1 := by
  simpa [reciprocalDensityMoment,reciprocalPolynomial] using reciprocalDensityMoment_eq hα hα1 0


theorem reciprocalMomentMeasure_probability {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    IsProbabilityMeasure (reciprocalMomentMeasure α) := by
  constructor
  rw [reciprocalMomentMeasure,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal
      (reciprocalMomentDensity_integrable hα hα1)
      (Eventually.of_forall (reciprocalMomentDensity_nonneg hα.le)),
    reciprocalMomentDensity_mass hα hα1,ENNReal.ofReal_one]

theorem reciprocalMomentMeasure_support {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    reciprocalMomentMeasure α (Icc 0 64)ᶜ=0 := by
  rw [reciprocalMomentMeasure,withDensity_apply _ measurableSet_Icc.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [self_mem_ae_restrict measurableSet_Icc.compl] with t ht
  rw [reciprocalMomentDensity_support hα hα1 ht,ENNReal.ofReal_zero]
  rfl

theorem reciprocalMomentDensity_power_integrable {α : ℝ} (hα : 0<α) (hα1 : α≤1) (n : ℕ) :
    Integrable (fun t:ℝ=>t^n*reciprocalMomentDensity α t) := by
  apply ((reciprocalMomentDensity_integrable hα hα1).const_mul (64^n:ℝ)).mono'
    (((measurable_id.pow_const n).mul (reciprocalMomentDensity_measurable α)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  change ‖t^n*reciprocalMomentDensity α t‖≤64^n*reciprocalMomentDensity α t
  simp only [norm_mul,Real.norm_eq_abs]
  rw [abs_of_nonneg (reciprocalMomentDensity_nonneg hα.le t)]
  by_cases ht : reciprocalMomentDensity α t=0
  · simp [ht]
  · have hs : t∈Icc 0 64 := by
      by_contra hn
      exact ht (reciprocalMomentDensity_support hα hα1 hn)
    rw [abs_pow,abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 n)
      (reciprocalMomentDensity_nonneg hα.le t)

theorem reciprocalMomentMeasure_moments {α : ℝ} (hα : 0<α) (hα1 : α≤1) (n : ℕ) :
    Integrable (fun t:ℝ=>t^n) (reciprocalMomentMeasure α) ∧
      (∫ t:ℝ,t^n ∂reciprocalMomentMeasure α)=reciprocalPolynomial n α := by
  have hm : Measurable (fun t=>ENNReal.ofReal (reciprocalMomentDensity α t)) :=
    (reciprocalMomentDensity_measurable α).ennreal_ofReal
  have hf : ∀ᵐ t:ℝ,ENNReal.ofReal (reciprocalMomentDensity α t)<∞ :=
    Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top)
  have hnon (t : ℝ) : (ENNReal.ofReal (reciprocalMomentDensity α t)).toReal=
      reciprocalMomentDensity α t := ENNReal.toReal_ofReal (reciprocalMomentDensity_nonneg hα.le t)
  constructor
  · unfold reciprocalMomentMeasure
    rw [integrable_withDensity_iff_integrable_smul' hm hf]
    simpa only [hnon,smul_eq_mul,mul_comm] using reciprocalMomentDensity_power_integrable hα hα1 n
  · rw [reciprocalMomentMeasure,integral_withDensity_eq_integral_toReal_smul hm hf]
    simpa only [hnon,smul_eq_mul,mul_comm,reciprocalDensityMoment] using reciprocalDensityMoment_eq hα hα1 n

/-- One actual compactly supported probability measure represents every original Apéry moment. -/
theorem apery_positive_moment_representation {x : ℝ} (hx : 1≤x) :
    HasPositiveMomentRepresentation x := by
  have hx0 : 0<x := by linarith
  have hα : 0<x⁻¹ := inv_pos.mpr hx0
  have hα1 : x⁻¹≤1 := (inv_le_one₀ hx0).mpr hx
  have hh := original_moments_of_reciprocal hα (by norm_num : (0:ℝ)≤64)
    (reciprocalMomentMeasure x⁻¹) (reciprocalMomentMeasure_probability hα hα1)
    (reciprocalMomentMeasure_support hα hα1) (reciprocalMomentMeasure_moments hα hα1)
  simpa only [inv_inv] using hh

end AperyMoments
