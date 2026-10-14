import AperyMoments.CauchyDomain

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem spectralCauchyTransform_norm_bound {b : ℝ} (hb : 0 ≤ b) {z : ℂ}
    (hz : 4+b < ‖z‖) : ‖spectralCauchyTransform b z‖ ≤ 1 / (‖z‖-(4+b)) := by
  have hδ : 0 < ‖z‖-(4+b) := sub_pos.mpr hz
  have hsep : ∀ t : ℝ, spectralDensity b t ≠ 0 → ‖z‖-(4+b) ≤ ‖z-t‖ := by
    intro t ht
    have hs := spectralDensity_support hb ht
    have hn := norm_add_le (z-(t:ℂ)) (t:ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at hn
    linarith
  have hh := spectralDensity_measurable b
  have hi := spectralDensity_integrable hb
  have hiK := densityCauchyKernel_integrable hh hi hδ hsep
  calc
    ‖spectralCauchyTransform b z‖ ≤ ∫ t : ℝ, ‖densityCauchyKernel (spectralDensity b) z t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, |spectralDensity b t| / (‖z‖-(4+b)) :=
      integral_mono hiK.norm (hi.abs.div_const _) (densityCauchyKernel_bound hδ hsep)
    _ = 1 / (‖z‖-(4+b)) := by
      simp_rw [abs_of_nonneg (spectralDensity_nonneg b _)]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, spectralDensity_integral hb]

theorem spectralCauchyTransform_norm_le_one {b : ℝ} (hb : 0 ≤ b) {z : ℂ}
    (hz : 5+b ≤ ‖z‖) : ‖spectralCauchyTransform b z‖ ≤ 1 := by
  have hδ : 0 < ‖z‖-(4+b) := by linarith
  apply (spectralCauchyTransform_norm_bound hb (by linarith)).trans
  rw [div_le_iff₀ hδ]
  linarith

end AperyMoments
