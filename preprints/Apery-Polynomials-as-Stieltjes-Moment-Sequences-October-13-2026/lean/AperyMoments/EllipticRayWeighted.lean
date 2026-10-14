import AperyMoments.EllipticRayScaling

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def ellipticRayWeightedBound : ℝ := (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
    (ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8)) +
  ((ellipticK (1 / 2) + 8) * (1 / 2 : ℝ) ^ (-(7 / 8 : ℝ))) *
    ∫ v in (0 : ℝ)..1, correctionWeight v

theorem ellipticRay_weighted_integrable {q : ℂ} (hq : q.im < 0) {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable (fun v : ℝ => ‖ellipticRayKernel q (A * v)‖ * correctionWeight v) volume 0 1 := by
  apply IntervalIntegrable.continuousOn_mul correctionWeight_integrable
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ellipticRay_scaled_continuousOn hq hA

theorem ellipticRayWeightedBound_nonneg : 0 ≤ ellipticRayWeightedBound := by
  have hK := ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)
  have hS := ellipticRaySmallBound_nonneg
  have hW : 0 ≤ ∫ v in (0 : ℝ)..1, correctionWeight v := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
  unfold ellipticRayWeightedBound
  positivity

theorem ellipticRay_weighted_bound {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (0 : ℝ)..1, ‖ellipticRayKernel q (A * v)‖ * correctionWeight v) ≤
      ellipticRayWeightedBound * A ^ (-(7 / 8 : ℝ)) := by
  have hA0 : 0 ≤ A := by linarith
  have hsub1 : uIcc (0 : ℝ) (1 / 2) ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hsub2 : uIcc (1 / 2 : ℝ) 1 ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hi := ellipticRay_weighted_integrable hq hA0
  have hf : IntervalIntegrable (fun v : ℝ => ‖ellipticRayKernel q (A * v)‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ellipticRay_scaled_continuousOn hq hA0
  have hi1 := IntervalIntegrable.mono_set hi hsub1
  have hi2 := IntervalIntegrable.mono_set hi hsub2
  have hw2 := IntervalIntegrable.mono_set correctionWeight_integrable hsub2
  have hfirst : (∫ v in (0 : ℝ)..(1 / 2), ‖ellipticRayKernel q (A * v)‖ * correctionWeight v) ≤
      (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8)) * A ^ (-(7 / 8 : ℝ))) := by
    calc
      _ ≤ ∫ v in (0 : ℝ)..(1 / 2), (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * ‖ellipticRayKernel q (A * v)‖ := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi1
          (IntervalIntegrable.const_mul (IntervalIntegrable.mono_set hf hsub1) _)
        intro v hv
        have hp : correctionWeight v ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          apply Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hv.2]) (by norm_num)
        nlinarith [norm_nonneg (ellipticRayKernel q (A * v))]
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (ellipticRay_scaled_integral_half hq hn hA) (by positivity)
  have hsecond : (∫ v in (1 / 2 : ℝ)..1, ‖ellipticRayKernel q (A * v)‖ * correctionWeight v) ≤
      ((ellipticK (1 / 2) + 8) * A ^ (-(7 / 8 : ℝ)) * (1 / 2 : ℝ) ^ (-(7 / 8 : ℝ))) *
        ∫ v in (0 : ℝ)..1, correctionWeight v := by
    calc
      _ ≤ ∫ v in (1 / 2 : ℝ)..1,
          ((ellipticK (1 / 2) + 8) * A ^ (-(7 / 8 : ℝ)) * (1 / 2 : ℝ) ^ (-(7 / 8 : ℝ))) * correctionWeight v := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi2 (IntervalIntegrable.const_mul hw2 _)
        intro v hv
        exact mul_le_mul_of_nonneg_right (ellipticRay_scaled_second_half hq hn hA hv.1)
          (Real.rpow_nonneg (sub_nonneg.mpr hv.2) _)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        apply mul_le_mul_of_nonneg_left _
        · have hK := ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)
          positivity
        · apply intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) le_rfl _ correctionWeight_integrable
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          exact Real.rpow_nonneg (sub_nonneg.mpr hv.2) _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  unfold ellipticRayWeightedBound
  nlinarith [hfirst, hsecond]

end AperyMoments
