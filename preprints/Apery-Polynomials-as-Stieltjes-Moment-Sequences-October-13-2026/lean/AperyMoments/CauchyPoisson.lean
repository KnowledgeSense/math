import AperyMoments.CauchyDomain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem affine_integral_pos (f : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    y * (∫ u : ℝ, f (x + y*u)) = ∫ t : ℝ, f t := by
  have he := Measure.integral_comp_mul_left (fun t => f (x+t)) y
  rw [abs_of_pos (inv_pos.mpr hy), smul_eq_mul] at he
  rw [he, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hy), one_mul]
  exact integral_add_left_eq_self f x

theorem densityCauchy_im_scaled {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {z : ℂ} (hz : 0 < z.im) :
    (densityCauchyTransform h z).im =
      -(∫ u : ℝ, h (z.re + z.im*u) * (1 + u^2)⁻¹) := by
  have hiK := densityCauchyKernel_integrable hh hi hz
    (fun t _ => by simpa only [abs_of_pos hz] using cauchy_separation_nonreal (ne_of_gt hz) t)
  have him := integral_im hiK
  change (∫ t : ℝ, (densityCauchyKernel h z t).im) = (∫ t : ℝ, densityCauchyKernel h z t).im at him
  rw [densityCauchyTransform, ← him]
  rw [← affine_integral_pos (fun t => (densityCauchyKernel h z t).im) z.re hz]
  rw [← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have hden : (z.re - (z.re + z.im*u))^2 + z.im^2 = z.im^2 * (1+u^2) := by ring
  have hu : (1 : ℝ) + u^2 ≠ 0 := by positivity
  simp only [densityCauchyKernel, Complex.div_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.sub_im, Complex.sub_re, sub_zero, zero_mul, Complex.normSq_apply]
  field_simp
  ring

theorem densityCauchy_im_tendsto_upper_bounded {h : ℝ → ℝ} (hh : Measurable h)
    (hi : Integrable h) {M : ℝ} (hM : ∀ t, |h t| ≤ M) {x : ℝ} (hc : ContinuousAt h x) :
    Tendsto (fun z : ℂ => (densityCauchyTransform h z).im)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (-Real.pi * h x)) := by
  have hlim : Tendsto (fun z : ℂ => ∫ u : ℝ, h (z.re + z.im*u) * (1+u^2)⁻¹)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (∫ u : ℝ, h x * (1+u^2)⁻¹)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => M * (1+u^2)⁻¹)
    · apply Eventually.of_forall
      intro z
      exact ((hh.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro z
      apply Eventually.of_forall
      intro u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1+u^2)⁻¹)]
      exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    · exact integrable_inv_one_add_sq.const_mul M
    · apply Eventually.of_forall
      intro u
      have ht : Tendsto (fun z : ℂ => z.re + z.im*u)
          (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 x) := by
        simpa using (show ContinuousAt (fun z : ℂ => z.re + z.im*u) (x : ℂ) by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
      exact (hc.tendsto.comp ht).mul_const _
  have he : (fun z : ℂ => -(∫ u : ℝ, h (z.re + z.im*u) * (1+u^2)⁻¹)) =ᶠ[
      𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)] (fun z => (densityCauchyTransform h z).im) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (densityCauchy_im_scaled hh hi hz).symm
  have hl := hlim.neg.congr' he
  convert hl using 1
  congr 1
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

end AperyMoments
