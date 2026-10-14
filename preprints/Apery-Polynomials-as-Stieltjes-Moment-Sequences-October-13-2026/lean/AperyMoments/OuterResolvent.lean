import AperyMoments.MomentTransform

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def outerResolvent (α : ℝ) (s : ℂ) : ℂ :=
  spectralCauchyTransform (2 * Real.sqrt α) (reciprocalMap α s) / Complex.sqrt s

theorem complexSqrt_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  apply Complex.ext
  · exact Complex.re_sqrt_ofReal
  · simp [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt, abs_of_nonneg hx]

theorem reciprocalMap_ofReal (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalMap α (x : ℂ) = (reciprocalRadius α x : ℂ) := by
  simp only [reciprocalMap, complexSqrt_ofReal_nonneg hx, reciprocalRadius, Complex.ofReal_add,
    Complex.ofReal_div]

theorem reciprocalRadius_large {α x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hx : 64 < x) :
    4 + 2 * Real.sqrt α < reciprocalRadius α x := by
  have hs : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  have hxp : 0 < x := by linarith
  have hsx := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hxp.le
  have h8 : 8 < Real.sqrt x := by nlinarith
  have hdiv : 0 < α / Real.sqrt x := by positivity
  unfold reciprocalRadius
  linarith

theorem outerResolvent_differentiableAt_real {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : 64 < x) : DifferentiableAt ℂ (outerResolvent α) (x : ℂ) := by
  have hxp : 0 < x := by linarith
  have hb : 0 ≤ 2 * Real.sqrt α := by positivity
  have hr := reciprocalRadius_large hα hα1 hx
  have hdom : reciprocalMap α (x : ℂ) ∈ cauchyDomain (4 + 2 * Real.sqrt α) := by
    right
    rw [reciprocalMap_ofReal α hxp.le, Complex.ofReal_re, abs_of_pos (by have := Real.sqrt_nonneg α; linarith : 0 < reciprocalRadius α x)]
    exact hr
  have hsl : (x : ℂ) ∈ Complex.slitPlane := Or.inl hxp
  have hn : Complex.sqrt (x : ℂ) ≠ 0 := by
    rw [complexSqrt_ofReal_nonneg hxp.le]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hxp))
  exact (((spectralCauchyTransform_analyticOnNhd hb _ hdom).differentiableAt).comp
    (x : ℂ) (reciprocalMap_differentiableAt α hsl)).div (Complex.differentiableAt_sqrt hsl) hn

theorem spectralCauchyTransform_real (b x : ℝ) :
    (spectralCauchyTransform b (x : ℂ)).im = 0 := by
  have he := densityCauchyTransform_conj (spectralDensity b) (x : ℂ)
  rw [Complex.conj_ofReal] at he
  have hi := congrArg Complex.im he
  change (spectralCauchyTransform b (x : ℂ)).im = -(spectralCauchyTransform b (x : ℂ)).im at hi
  linarith

theorem outerResolvent_real (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (outerResolvent α (x : ℂ)).im = 0 := by
  simp only [outerResolvent, reciprocalMap_ofReal α hx, complexSqrt_ofReal_nonneg hx,
    Complex.div_im, spectralCauchyTransform_real, Complex.ofReal_im, zero_mul, mul_zero, sub_self,
    zero_div]

theorem momentTransform_positive (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    momentTransform α (x : ℂ) = outerResolvent α (x : ℂ) := by
  simp [momentTransform, not_lt.mpr hx, outerResolvent]

theorem momentTransform_outer_upper (α : ℝ) {s : ℂ} (hs : 0 < s.im) (hn : α < ‖s‖) :
    momentTransform α s = outerResolvent α s := by
  rw [momentTransform_upper α hs, reciprocalResolvent_outer hs hn]
  rfl

theorem momentTransform_outer_lower (α : ℝ) {s : ℂ} (hs : s.im < 0) (hn : α < ‖s‖) :
    momentTransform α s = starRingEnd ℂ (outerResolvent α (starRingEnd ℂ s)) := by
  rw [momentTransform_lower α hs, reciprocalResolvent_outer (by simpa using neg_pos.mpr hs)
    (by simpa using hn)]
  rfl

end AperyMoments
