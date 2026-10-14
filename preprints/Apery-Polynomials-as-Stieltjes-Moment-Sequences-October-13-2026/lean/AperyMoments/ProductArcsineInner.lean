import AperyMoments.PositiveArcsine
import AperyMoments.CorrectionCutSplit

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem productArcsine_scale_jacobian {r t : ℝ} (hr : 0 < r) (hr1 : r < 1) (ht : t ∈ Icc 0 1) :
    r * productArcsineKernel (r * t) r = positiveArcsineWeight r * positiveArcsineWeight t := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold productArcsineKernel positiveArcsineWeight
  rw [show (1 - r ^ 2) * (r ^ 2 - (r * t) ^ 2) = r ^ 2 * ((1 - r ^ 2) * (1 - t ^ 2)) by ring,
    Real.mul_rpow (sq_nonneg _) (mul_nonneg h1 h2), Real.mul_rpow h1 h2,
    ← Real.rpow_natCast_mul hr.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

theorem productArcsine_inner_integral (F : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ z in (0 : ℝ)..r, F z * (productArcsineKernel z r : ℂ)) =
      positiveArcsineWeight r • ∫ t in (0 : ℝ)..1, F (r * t) * (positiveArcsineWeight t : ℂ) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun z => F z * (productArcsineKernel z r : ℂ)) r
  simp only [mul_zero, mul_one] at h
  rw [← h, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only
  rw [Complex.real_smul, Complex.real_smul]
  have he := congrArg Complex.ofReal (productArcsine_scale_jacobian hr hr1 ht)
  push_cast at he
  calc
    _ = F (r * t) * ((r : ℂ) * (productArcsineKernel (r * t) r : ℂ)) := by ring
    _ = _ := by rw [he]; ring

theorem productArcsine_scaled_integrable {F : ℝ → ℂ} (hF : Continuous F) (r : ℝ) :
    IntervalIntegrable (fun t => F (r * t) * (positiveArcsineWeight t : ℂ)) volume 0 1 := by
  have hi : IntervalIntegrable (fun t => (positiveArcsineWeight t : ℂ)) volume 0 1 :=
    ⟨positiveArcsine_integrable.1.ofReal, positiveArcsine_integrable.2.ofReal⟩
  apply IntervalIntegrable.continuousOn_mul hi
  exact (hF.comp (continuous_const.mul continuous_id)).continuousOn

theorem productArcsine_inner_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (fun z => F z * (productArcsineKernel z r : ℂ)) volume 0 r := by
  have hi := IntervalIntegrable.smul (productArcsine_scaled_integrable hF r) (positiveArcsineWeight r)
  have hj : IntervalIntegrable (fun t => r • (F (r * t) * (productArcsineKernel (r * t) r : ℂ))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi ⊢
    apply (integrableOn_congr_fun _ measurableSet_Ioo).mp hi
    intro t ht
    dsimp only [Pi.smul_apply]
    rw [Complex.real_smul, Complex.real_smul]
    have he := congrArg Complex.ofReal (productArcsine_scale_jacobian hr hr1 ⟨ht.1.le, ht.2.le⟩)
    push_cast at he
    calc
      _ = F (r * t) * ((positiveArcsineWeight r : ℂ) * (positiveArcsineWeight t : ℂ)) := by ring
      _ = F (r * t) * ((r : ℂ) * (productArcsineKernel (r * t) r : ℂ)) := by rw [he]
      _ = _ := by ring
  have h := (affine_intervalIntegrable_iff (fun z => F z * (productArcsineKernel z r : ℂ)) 0 hr).mpr (by
    simpa only [zero_add] using hj)
  simpa only [zero_add] using h

theorem productArcsine_scaled_norm_integral_bound {F : ℝ → ℂ} (hF : Continuous F)
    {M r : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ M) (hr : r ∈ Icc 0 1) :
    (∫ t in (0 : ℝ)..1, ‖F (r * t) * (positiveArcsineWeight t : ℂ)‖) ≤ M * (Real.pi / 2) := by
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, M * positiveArcsineWeight t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (productArcsine_scaled_integrable hF r).norm
        (IntervalIntegrable.const_mul positiveArcsine_integrable M)
      intro t ht
      have hrt : r * t ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hr.1 ht.1, (mul_le_mul_of_nonneg_left ht.2 hr.1).trans (by simpa using hr.2)⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (positiveArcsineWeight_nonneg ht)]
      exact mul_le_mul_of_nonneg_right (hM _ hrt) (positiveArcsineWeight_nonneg ht)
    _ = _ := by rw [intervalIntegral.integral_const_mul, positiveArcsine_integral]

end AperyMoments
