import AperyMoments.SpectralMeasure

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem spectralTestKernel_integral_theta (b : ℝ) (F : ℝ → ℂ) (w : ℝ) :
    (∫ θ in Ioc (0 : ℝ) Real.pi, spectralTestKernel b F θ w) =
      (Real.pi : ℂ) * (F w * (spectralDensity b w : ℂ)) := by
  unfold spectralTestKernel spectralDensity
  rw [integral_const_mul, integral_complex_ofReal,
    intervalIntegral.integral_of_le Real.pi_pos.le]
  push_cast
  field_simp

theorem spectralTest_integrable {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) :
    Integrable (fun w => F w * (spectralDensity b w : ℂ)) := by
  have h := (spectralTestKernel_integrable hb hF hM).integral_prod_right
  have hi := h.const_mul (Real.pi : ℂ)⁻¹
  have he : (fun w => (Real.pi : ℂ)⁻¹ * ∫ θ in Ioc (0 : ℝ) Real.pi, spectralTestKernel b F θ w) =
      (fun w => F w * (spectralDensity b w : ℂ)) := by
    funext w
    rw [spectralTestKernel_integral_theta, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]
  rwa [he] at hi

theorem spectralTestKernel_integral_translate (b : ℝ) (F : ℝ → ℂ) (θ : ℝ) :
    (∫ w : ℝ, spectralTestKernel b F θ w) =
      ∫ c : ℝ, F (c + b * Real.cos θ) * (latticeDensity c : ℂ) := by
  have h := integral_add_right_eq_self (μ := volume) (spectralTestKernel b F θ) (b * Real.cos θ)
  simpa only [spectralTestKernel, add_sub_cancel_right] using h.symm

theorem spectralTest_integral {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖F w‖ ≤ M) :
    (∫ w : ℝ, F w * (spectralDensity b w : ℂ)) =
      (Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
        ∫ c : ℝ, F (c + b * Real.cos θ) * (latticeDensity c : ℂ) := by
  have h := integral_integral_swap (f := spectralTestKernel b F) (spectralTestKernel_integrable hb hF hM)
  have hr : (∫ w : ℝ, ∫ θ in Ioc (0 : ℝ) Real.pi, spectralTestKernel b F θ w) =
      (Real.pi : ℂ) * ∫ w : ℝ, F w * (spectralDensity b w : ℂ) := by
    simp_rw [spectralTestKernel_integral_theta]
    exact integral_const_mul _ _
  rw [hr] at h
  simp_rw [spectralTestKernel_integral_translate] at h
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

theorem spectralTest_integral_real {b M : ℝ} (hb : 0 ≤ b) {F : ℝ → ℝ}
    (hF : Continuous F) (hM : ∀ w ∈ Icc (-(4 + b)) (4 + b), |F w| ≤ M) :
    (∫ w : ℝ, F w * spectralDensity b w) =
      Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
        ∫ c : ℝ, F (c + b * Real.cos θ) * latticeDensity c := by
  have h := spectralTest_integral hb (Complex.continuous_ofReal.comp hF)
    (show ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖(F w : ℂ)‖ ≤ M from by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hM)
  simp only [Function.comp_def, ← Complex.ofReal_mul, integral_complex_ofReal,
    intervalIntegral.integral_ofReal, ← Complex.ofReal_inv] at h
  exact Complex.ofReal_injective h

theorem spectralDensity_integrable {b : ℝ} (hb : 0 ≤ b) : Integrable (spectralDensity b) := by
  have hi := spectralTest_integrable hb (show Continuous (fun _ : ℝ => (1 : ℂ)) from continuous_const)
    (show ∀ w ∈ Icc (-(4 + b)) (4 + b), ‖(1 : ℂ)‖ ≤ 1 by intros; norm_num)
  have hr := hi.re
  change Integrable (fun w : ℝ => ((1 : ℂ) * (spectralDensity b w : ℂ)).re) at hr
  simpa only [one_mul, Complex.ofReal_re] using hr

theorem spectralDensity_integral {b : ℝ} (hb : 0 ≤ b) : (∫ w : ℝ, spectralDensity b w) = 1 := by
  have h := spectralTest_integral_real hb (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const)
    (show ∀ w ∈ Icc (-(4 + b)) (4 + b), |(1 : ℝ)| ≤ 1 by intros; norm_num)
  simpa [latticeDensity_integral] using h

end AperyMoments
