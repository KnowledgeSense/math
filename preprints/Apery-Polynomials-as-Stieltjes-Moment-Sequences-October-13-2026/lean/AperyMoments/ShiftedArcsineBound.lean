import AperyMoments.ShiftedPowerIntegral

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def shiftedArcsineMajorant (a v : ℝ) : ℝ :=
  ‖v-a‖^(-(1/2 : ℝ))/4 + (1-v)^(-(2/3 : ℝ))/(4/3)

def shiftedArcsineBound : ℝ :=
  (∫ t in (-3 : ℝ)..3, ‖t‖^(-(1/2 : ℝ)))/4 +
    (∫ v in (0 : ℝ)..1, (1-v)^(-(2/3 : ℝ)))/(4/3)

theorem shiftedArcsineMajorant_nonneg {a v : ℝ} (hv : v ≤ 1) :
    0 ≤ shiftedArcsineMajorant a v := by
  unfold shiftedArcsineMajorant
  exact add_nonneg (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num))
    (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hv) _) (by norm_num))

theorem shiftedArcsineMajorant_integrable (a : ℝ) :
    IntervalIntegrable (shiftedArcsineMajorant a) volume 0 1 :=
  ((shiftedPower_integrable (by norm_num : (1/2 : ℝ)<1) a).div_const 4).add
    ((endpointPower_integrable (by norm_num : (2/3 : ℝ)<1)).div_const (4/3))

theorem shiftedArcsine_power_bound {a v : ℝ} (hv : v ≤ 1) :
    ‖v-a‖^(-(1/8 : ℝ))*(1-v)^(-(1/2 : ℝ)) ≤ shiftedArcsineMajorant a v := by
  have h := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg (norm_nonneg (v-a)) (-(1/8 : ℝ)))
    (Real.rpow_nonneg (sub_nonneg.mpr hv) (-(1/2 : ℝ)))
    (show (4 : ℝ).HolderConjugate (4/3) by rw [Real.holderConjugate_iff]; norm_num)
  rw [← Real.rpow_mul (norm_nonneg (v-a)), ← Real.rpow_mul (sub_nonneg.mpr hv)] at h
  norm_num at h
  exact h

theorem shiftedArcsine_integral_bound {a : ℝ} (ha : |a| ≤ 2) :
    (∫ v in (0 : ℝ)..1, shiftedArcsineMajorant a v) ≤ shiftedArcsineBound := by
  have ha' := abs_le.mp ha
  have hp : (∫ v in (0 : ℝ)..1, ‖v-a‖^(-(1/2 : ℝ))) ≤
      ∫ t in (-3 : ℝ)..3, ‖t‖^(-(1/2 : ℝ)) := by
    rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => ‖t‖^(-(1/2 : ℝ)))]
    apply intervalIntegral.integral_mono_interval
    · linarith [ha'.2]
    · linarith
    · linarith [ha'.1]
    · exact Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg t) _)
    · exact norm_rpow_intervalIntegrable (by norm_num : (1/2 : ℝ)<1) _ _
  unfold shiftedArcsineMajorant shiftedArcsineBound
  rw [intervalIntegral.integral_add
    ((shiftedPower_integrable (by norm_num : (1/2 : ℝ)<1) a).div_const 4)
    ((endpointPower_integrable (by norm_num : (2/3 : ℝ)<1)).div_const (4/3)),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  linarith

theorem shiftedArcsineBound_nonneg : 0 ≤ shiftedArcsineBound := by
  apply le_trans _ (shiftedArcsine_integral_bound (a := 0) (by norm_num))
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro v hv
  exact shiftedArcsineMajorant_nonneg hv.2

end AperyMoments
