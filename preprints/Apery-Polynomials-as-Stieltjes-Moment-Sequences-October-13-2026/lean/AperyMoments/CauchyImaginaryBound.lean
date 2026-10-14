import AperyMoments.CauchyPoisson
import AperyMoments.CauchyImaginaryBoundary
import AperyMoments.CauchySymmetry
import AperyMoments.SpectralDensityBounded

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem densityCauchy_im_bound_upper {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {M : ℝ} (hM : ∀ t, |h t| ≤ M) {z : ℂ} (hz : 0 < z.im) :
    |(densityCauchyTransform h z).im| ≤ M*Real.pi := by
  rw [densityCauchy_im_scaled hh hi hz, abs_neg, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ u : ℝ, M*(1+u^2)⁻¹ := by
      apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul M)
      apply Eventually.of_forall
      intro u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1+u^2)⁻¹)]
      exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem densityCauchy_im_bound {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {M : ℝ} (hM : ∀ t, |h t| ≤ M) (z : ℂ) : |(densityCauchyTransform h z).im| ≤ M*Real.pi := by
  rcases lt_trichotomy z.im 0 with hz | hz | hz
  · have hc : 0 < (starRingEnd ℂ z).im := by simpa using neg_pos.mpr hz
    have he := densityCauchy_im_bound_upper hh hi hM hc
    rw [densityCauchyTransform_conj] at he
    simpa using he
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [he, densityCauchyTransform_real, abs_zero]
    exact mul_nonneg ((abs_nonneg (h 0)).trans (hM 0)) Real.pi_pos.le
  · exact densityCauchy_im_bound_upper hh hi hM hz

theorem spectralCauchy_im_bounded {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |(spectralCauchyTransform b z).im| ≤ C := by
  obtain ⟨M,hM0,hM⟩ := spectralDensity_bounded hb hb2
  exact ⟨M*Real.pi,mul_nonneg hM0 Real.pi_pos.le,
    densityCauchy_im_bound (spectralDensity_measurable b) (spectralDensity_integrable hb.le) hM⟩

end AperyMoments
