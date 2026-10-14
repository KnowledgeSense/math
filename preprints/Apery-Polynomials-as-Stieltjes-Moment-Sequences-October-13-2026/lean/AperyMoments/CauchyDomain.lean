import AperyMoments.CauchyTransform

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def cauchyDomain (B : ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ B < |z.re|}

theorem cauchyDomain_isOpen (B : ℝ) : IsOpen (cauchyDomain B) :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const Complex.continuous_re.abs)

theorem cauchy_separation_nonreal {z : ℂ} (_hz : z.im ≠ 0) (t : ℝ) :
    |z.im| ≤ ‖z - t‖ := by
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using Complex.abs_im_le_norm (z - t)

theorem cauchy_separation_outside {B : ℝ} {z : ℂ} {t : ℝ} (ht : |t| ≤ B) :
    |z.re| - B ≤ ‖z - t‖ := by
  have h := abs_sub_abs_le_abs_sub z.re t
  have h' := Complex.abs_re_le_norm (z - t)
  simp only [Complex.sub_re, Complex.ofReal_re] at h'
  linarith

theorem densityCauchyTransform_analyticOnNhd {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {B : ℝ} (hs : ∀ t, h t ≠ 0 → |t| ≤ B) :
    AnalyticOnNhd ℂ (densityCauchyTransform h) (cauchyDomain B) := by
  apply DifferentiableOn.analyticOnNhd _ (cauchyDomain_isOpen B)
  intro z hz
  rcases hz with hz | hz
  · exact (densityCauchyTransform_differentiableAt hh hi (abs_pos.mpr hz)
      (fun t _ => cauchy_separation_nonreal hz t)).differentiableWithinAt
  · exact (densityCauchyTransform_differentiableAt hh hi (sub_pos.mpr hz)
      (fun t ht => cauchy_separation_outside (hs t ht))).differentiableWithinAt

def spectralCauchyTransform (b : ℝ) : ℂ → ℂ := densityCauchyTransform (spectralDensity b)

theorem spectralDensity_support {b t : ℝ} (hb : 0 ≤ b) (ht : spectralDensity b t ≠ 0) :
    |t| ≤ 4 + b := by
  by_contra h
  exact ht (spectralDensity_eq_zero_of_abs_ge hb (le_of_not_ge h))

theorem spectralCauchyTransform_analyticOnNhd {b : ℝ} (hb : 0 ≤ b) :
    AnalyticOnNhd ℂ (spectralCauchyTransform b) (cauchyDomain (4 + b)) :=
  densityCauchyTransform_analyticOnNhd (spectralDensity_measurable b) (spectralDensity_integrable hb)
    (fun _ ht => spectralDensity_support hb ht)

theorem spectralCauchyKernel_integrable {b : ℝ} (hb : 0 ≤ b) {z : ℂ}
    (hz : z ∈ cauchyDomain (4 + b)) : Integrable (densityCauchyKernel (spectralDensity b) z) := by
  rcases hz with hz | hz
  · exact densityCauchyKernel_integrable (spectralDensity_measurable b) (spectralDensity_integrable hb)
      (abs_pos.mpr hz) (fun t _ => cauchy_separation_nonreal hz t)
  · exact densityCauchyKernel_integrable (spectralDensity_measurable b) (spectralDensity_integrable hb)
      (sub_pos.mpr hz) (fun _ ht => cauchy_separation_outside (spectralDensity_support hb ht))

end AperyMoments
