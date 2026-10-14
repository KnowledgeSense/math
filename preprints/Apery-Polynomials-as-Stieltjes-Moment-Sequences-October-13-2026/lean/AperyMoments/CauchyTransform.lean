import AperyMoments.SpectralMoments
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def densityCauchyKernel (h : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ := (h t : ℂ) / (z - t)
def densityCauchyDerivative (h : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ := -(h t : ℂ) / (z - t) ^ 2
def densityCauchyTransform (h : ℝ → ℝ) (z : ℂ) : ℂ := ∫ t : ℝ, densityCauchyKernel h z t

theorem densityCauchyKernel_measurable {h : ℝ → ℝ} (hh : Measurable h) (z : ℂ) :
    Measurable (densityCauchyKernel h z) := by
  unfold densityCauchyKernel
  exact (Complex.continuous_ofReal.measurable.comp hh).div (by fun_prop)

theorem densityCauchyDerivative_measurable {h : ℝ → ℝ} (hh : Measurable h) (z : ℂ) :
    Measurable (densityCauchyDerivative h z) := by
  unfold densityCauchyDerivative
  exact (Complex.continuous_ofReal.measurable.comp hh).neg.div (by fun_prop)

theorem densityCauchyKernel_bound {h : ℝ → ℝ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t, h t ≠ 0 → δ ≤ ‖z - t‖) (t : ℝ) :
    ‖densityCauchyKernel h z t‖ ≤ |h t| / δ := by
  by_cases ht : h t = 0
  · simp [densityCauchyKernel, ht]
  · unfold densityCauchyKernel
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hδ (hsep t ht)

theorem densityCauchyDerivative_bound {h : ℝ → ℝ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t, h t ≠ 0 → δ ≤ ‖z - t‖) (t : ℝ) :
    ‖densityCauchyDerivative h z t‖ ≤ |h t| / δ ^ 2 := by
  by_cases ht : h t = 0
  · simp [densityCauchyDerivative, ht]
  · unfold densityCauchyDerivative
    rw [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ)
    nlinarith [hsep t ht, norm_nonneg (z - t)]

theorem densityCauchyKernel_integrable {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t, h t ≠ 0 → δ ≤ ‖z - t‖) :
    Integrable (densityCauchyKernel h z) :=
  (hi.abs.div_const δ).mono' (densityCauchyKernel_measurable hh z).aestronglyMeasurable
    (Eventually.of_forall (densityCauchyKernel_bound hδ hsep))

theorem densityCauchyKernel_hasDerivAt {h : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (hsep : h t ≠ 0 → z - t ≠ 0) :
    HasDerivAt (fun w => densityCauchyKernel h w t) (densityCauchyDerivative h z t) z := by
  by_cases ht : h t = 0
  · simpa only [densityCauchyKernel, densityCauchyDerivative, ht, Complex.ofReal_zero, neg_zero, zero_div] using
      (hasDerivAt_const z (0 : ℂ))
  · have hd := ((hasDerivAt_id z).sub_const (t : ℂ)).inv (hsep ht)
    have hd' := hd.const_mul (h t : ℂ)
    convert hd' using 1
    · funext w
      simp only [densityCauchyKernel, div_eq_mul_inv, Pi.inv_apply, id_eq]
    · unfold densityCauchyDerivative
      simp only [one_mul, div_eq_mul_inv, neg_mul, mul_neg, id_eq]

theorem densityCauchyTransform_differentiableAt {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ t, h t ≠ 0 → δ ≤ ‖z - t‖) :
    DifferentiableAt ℂ (densityCauchyTransform h) z := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hnear : ∀ w ∈ ball z (δ / 2), ∀ t, h t ≠ 0 → δ / 2 ≤ ‖w - t‖ := by
    intro w hw t ht
    have hd : ‖z - w‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
    have hn := norm_add_le (z - w) (w - (t : ℂ))
    rw [sub_add_sub_cancel] at hn
    linarith [hsep t ht]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := densityCauchyKernel h) (F' := densityCauchyDerivative h) (μ := volume)
    (bound := fun t => |h t| / (δ / 2) ^ 2) (s := ball z (δ / 2)) (ball_mem_nhds z hδ2)
    (Eventually.of_forall fun w => (densityCauchyKernel_measurable hh w).aestronglyMeasurable)
    (densityCauchyKernel_integrable hh hi hδ hsep)
    (densityCauchyDerivative_measurable hh z).aestronglyMeasurable
    (Eventually.of_forall fun t w hw => densityCauchyDerivative_bound hδ2 (hnear w hw) t)
    (hi.abs.div_const _)
    (Eventually.of_forall fun t w hw => densityCauchyKernel_hasDerivAt (fun ht =>
      norm_pos_iff.mp (hδ2.trans_le (hnear w hw t ht))))
  exact hd.2.differentiableAt

end AperyMoments
