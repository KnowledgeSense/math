import AperyMoments.ProductArcsineTriangle

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

theorem productTriangle_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => productTriangle F p.1 p.2)
      ((volume.restrict (Ioo 0 1)).prod (volume.restrict (Ioo 0 1))) := by
  have hm := (productTriangle_measurable hF).aestronglyMeasurable
    (μ := (volume.restrict (Ioo 0 1)).prod (volume.restrict (Ioo 0 1)))
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact productTriangle_inner_integrable hF hr.1 hr.2
  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp positiveArcsine_integrable
    apply (hi.mul_const (M * (Real.pi / 2))).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      productTriangle_inner_norm_integral hr.1 hr.2]
    exact productArcsine_inner_norm_bound hF hM hr.1 hr.2

theorem productTriangle_integral_right (F : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ z in Ioo (0 : ℝ) 1, productTriangle F r z) =
      positiveArcsineWeight r • ∫ t in (0 : ℝ)..1, F (r * t) * (positiveArcsineWeight t : ℂ) := by
  unfold productTriangle
  rw [integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl hr1.le),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  exact productArcsine_inner_integral F hr hr1

theorem productTriangle_integral_left (F : ℝ → ℂ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (∫ r in Ioo (0 : ℝ) 1, productTriangle F r z) =
      F z * (ellipticK (1 - z ^ 2) : ℂ) := by
  have he : (∫ r in Ioo (0 : ℝ) 1, productTriangle F r z) =
      ∫ r in Ioo (0 : ℝ) 1,
        (Ioo z 1).indicator (fun r => F z * (productArcsineKernel z r : ℂ)) r := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    by_cases hzr : z < r
    · simp only [productTriangle, indicator_of_mem (show z ∈ Ioo 0 r from ⟨hz, hzr⟩),
        indicator_of_mem (show r ∈ Ioo z 1 from ⟨hzr, hr.2⟩)]
    · simp only [productTriangle, indicator_of_notMem (show z ∉ Ioo 0 r from fun h => hzr h.2),
        indicator_of_notMem (show r ∉ Ioo z 1 from fun h => hzr h.1)]
  rw [he, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (Ioo_subset_Ioo hz.le le_rfl),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hz1.le,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, productArcsine_integral hz hz1]

/-- The elliptic density is derived from the product of two actual positive arcsine integrals. -/
theorem productArcsine_test_integral {F : ℝ → ℂ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M) :
    (∫ z in Ioo (0 : ℝ) 1, F z * (ellipticK (1 - z ^ 2) : ℂ)) =
      ∫ r in Ioo (0 : ℝ) 1,
        positiveArcsineWeight r • ∫ t in (0 : ℝ)..1, F (r * t) * (positiveArcsineWeight t : ℂ) := by
  have h := integral_integral_swap (f := productTriangle F) (productTriangle_integrable hF hM)
  change (∫ r in Ioo (0 : ℝ) 1, ∫ z in Ioo (0 : ℝ) 1, productTriangle F r z) =
    (∫ z in Ioo (0 : ℝ) 1, ∫ r in Ioo (0 : ℝ) 1, productTriangle F r z) at h
  calc
    _ = ∫ z in Ioo (0 : ℝ) 1, ∫ r in Ioo (0 : ℝ) 1, productTriangle F r z := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro z hz
      exact (productTriangle_integral_left F hz.1 hz.2).symm
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ z in Ioo (0 : ℝ) 1, productTriangle F r z := h.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      exact productTriangle_integral_right F hr.1 hr.2

theorem productArcsine_test_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M) :
    IntegrableOn (fun z => F z * (ellipticK (1 - z ^ 2) : ℂ)) (Ioo 0 1) := by
  have hi := (productTriangle_integrable hF hM).integral_prod_right
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact productTriangle_integral_left F hz.1 hz.2

theorem productArcsine_test_integral_real {F : ℝ → ℝ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M) :
    (∫ z in Ioo (0 : ℝ) 1, F z * ellipticK (1 - z ^ 2)) =
      ∫ r in Ioo (0 : ℝ) 1,
        positiveArcsineWeight r * ∫ t in (0 : ℝ)..1, F (r * t) * positiveArcsineWeight t := by
  have h := productArcsine_test_integral (Complex.continuous_ofReal.comp hF)
    (show ∀ t ∈ Icc (0 : ℝ) 1, ‖(F t : ℂ)‖ ≤ M from by simpa only [Complex.norm_real, Real.norm_eq_abs] using hM)
  simp only [Function.comp_def, Complex.real_smul, ← Complex.ofReal_mul, intervalIntegral.integral_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end AperyMoments
