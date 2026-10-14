import AperyMoments.ProductArcsineInner
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def productTriangle (F : ℝ → ℂ) (r z : ℝ) : ℂ :=
  (Ioo 0 r).indicator (fun z => F z * (productArcsineKernel z r : ℂ)) z

theorem productArcsineKernel_nonneg {r z : ℝ} (hr : r ∈ Icc 0 1) (hz : z ∈ Icc 0 r) :
    0 ≤ productArcsineKernel z r := by
  apply Real.rpow_nonneg
  apply mul_nonneg <;> nlinarith [hr.1, hr.2, hz.1, hz.2]

theorem productArcsine_inner_integral_real (F : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ z in (0 : ℝ)..r, F z * productArcsineKernel z r) =
      positiveArcsineWeight r * ∫ t in (0 : ℝ)..1, F (r * t) * positiveArcsineWeight t := by
  have h := productArcsine_inner_integral (fun z => (F z : ℂ)) hr hr1
  simp only [Complex.real_smul, ← Complex.ofReal_mul, intervalIntegral.integral_ofReal] at h
  exact Complex.ofReal_injective h

theorem productArcsine_inner_norm_bound {F : ℝ → ℂ} (hF : Continuous F)
    {M r : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M) (hr : 0 < r) (hr1 : r < 1) :
    (∫ z in (0 : ℝ)..r, ‖F z * (productArcsineKernel z r : ℂ)‖) ≤
      positiveArcsineWeight r * (M * (Real.pi / 2)) := by
  have he : (∫ z in (0 : ℝ)..r, ‖F z * (productArcsineKernel z r : ℂ)‖) =
      ∫ z in (0 : ℝ)..r, ‖F z‖ * productArcsineKernel z r := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hr.le] at hz
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (productArcsineKernel_nonneg ⟨hr.le, hr1.le⟩ hz)]
  rw [he, productArcsine_inner_integral_real (fun z => ‖F z‖) hr hr1]
  have hh : (∫ t in (0 : ℝ)..1, ‖F (r * t)‖ * positiveArcsineWeight t) ≤ M * (Real.pi / 2) := by
    have h := productArcsine_scaled_norm_integral_bound hF hM ⟨hr.le, hr1.le⟩
    convert h using 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (positiveArcsineWeight_nonneg ht)]
  exact mul_le_mul_of_nonneg_left hh (positiveArcsineWeight_nonneg ⟨hr.le, hr1.le⟩)

theorem productTriangle_measurable {F : ℝ → ℂ} (hF : Continuous F) :
    Measurable (fun p : ℝ × ℝ => productTriangle F p.1 p.2) := by
  simp only [productTriangle, Set.indicator_apply, Set.mem_Ioo]
  change Measurable (fun p : ℝ × ℝ => if 0 < p.2 ∧ p.2 < p.1 then
    F p.2 * (productArcsineKernel p.2 p.1 : ℂ) else 0)
  apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_fst))
  · unfold productArcsineKernel
    fun_prop
  · exact measurable_const

theorem productTriangle_inner_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IntegrableOn (productTriangle F r) (Ioo 0 1) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mp (productArcsine_inner_integrable hF hr hr1)
  exact (hi.integrable_indicator measurableSet_Ioo).integrableOn

theorem productTriangle_inner_norm_integral {F : ℝ → ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ z in Ioo (0 : ℝ) 1, ‖productTriangle F r z‖) =
      ∫ z in (0 : ℝ)..r, ‖F z * (productArcsineKernel z r : ℂ)‖ := by
  have he : (fun z => ‖productTriangle F r z‖) =
      (Ioo 0 r).indicator (fun z => ‖F z * (productArcsineKernel z r : ℂ)‖) := by
    funext z
    by_cases hz : z ∈ Ioo 0 r <;> simp [productTriangle, hz]
  rw [he, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl hr1.le),
    intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]

end AperyMoments
