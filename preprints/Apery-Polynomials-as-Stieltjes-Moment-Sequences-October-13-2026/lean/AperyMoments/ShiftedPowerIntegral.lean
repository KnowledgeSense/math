import AperyMoments.SquareRootSingularity
import Mathlib.Analysis.MeanInequalities

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem norm_rpow_locallyIntegrable {p : ℝ} (hp : p < 1) :
    LocallyIntegrable (fun t : ℝ => ‖t‖ ^ (-p)) volume := by
  apply locallyIntegrable_of_norm_le_rpow (E := ℝ) (C := 1) (α := p) (by simp) (by simpa using hp)
  · exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg t) _), one_mul]
  · exact (measurable_id.norm.pow measurable_const).aestronglyMeasurable

theorem norm_rpow_intervalIntegrable {p : ℝ} (hp : p < 1) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖t‖ ^ (-p)) volume a b := by
  have hi := (norm_rpow_locallyIntegrable hp).integrableOn_isCompact (k := uIcc a b) isCompact_uIcc
  exact ⟨hi.mono_set (fun t ht => ⟨(min_le_left a b).trans ht.1.le, ht.2.trans (le_max_right a b)⟩),
    hi.mono_set (fun t ht => ⟨(min_le_right a b).trans ht.1.le, ht.2.trans (le_max_left a b)⟩)⟩

def shiftedPowerBound (p : ℝ) : ℝ := ∫ t in (-2 : ℝ)..2, ‖t‖ ^ (-p)

theorem shiftedPowerBound_nonneg (p : ℝ) : 0 ≤ shiftedPowerBound p := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact Real.rpow_nonneg (norm_nonneg t) _

theorem shiftedPower_integrable {p : ℝ} (hp : p < 1) (a : ℝ) :
    IntervalIntegrable (fun v : ℝ => ‖v - a‖ ^ (-p)) volume 0 1 := by
  have h := (norm_rpow_intervalIntegrable hp (-a) (1 - a)).comp_sub_right a
  simpa using h

theorem shiftedPower_integral_le {p a : ℝ} (hp : p < 1) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (∫ v in (0 : ℝ)..1, ‖v - a‖ ^ (-p)) ≤ shiftedPowerBound p := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => ‖t‖ ^ (-p))]
  unfold shiftedPowerBound
  apply intervalIntegral.integral_mono_interval
  · linarith
  · linarith
  · linarith
  · exact Eventually.of_forall fun t => Real.rpow_nonneg (norm_nonneg t) _
  · exact norm_rpow_intervalIntegrable hp _ _

theorem weak_singularity_weight_bound {a v : ℝ} (hv : v ≤ 1) :
    ‖v - a‖ ^ (-(1 / 16 : ℝ)) * (1 - v) ^ (-(1 / 2 : ℝ)) ≤
      ‖v - a‖ ^ (-(1 / 4 : ℝ)) / 4 + (1 - v) ^ (-(2 / 3 : ℝ)) / (4 / 3) := by
  have h := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg (norm_nonneg (v - a)) (-(1 / 16 : ℝ)))
    (Real.rpow_nonneg (sub_nonneg.mpr hv) (-(1 / 2 : ℝ)))
    (show (4 : ℝ).HolderConjugate (4 / 3) by rw [Real.holderConjugate_iff]; norm_num)
  rw [← Real.rpow_mul (norm_nonneg (v - a)), ← Real.rpow_mul (sub_nonneg.mpr hv)] at h
  norm_num at h ⊢
  exact h

theorem endpointPower_integrable {p : ℝ} (hp : p < 1) :
    IntervalIntegrable (fun v : ℝ => (1 - v) ^ (-p)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (show (-1 : ℝ) < -p by linarith)).comp_sub_left 1
  simpa only [sub_zero, sub_self] using h.symm

def weakSingularityBound : ℝ := shiftedPowerBound (1 / 4) / 4 +
  (∫ v in (0 : ℝ)..1, (1 - v) ^ (-(2 / 3 : ℝ))) / (4 / 3)

theorem weakSingularityBound_nonneg : 0 ≤ weakSingularityBound := by
  unfold weakSingularityBound
  have h : 0 ≤ ∫ v in (0 : ℝ)..1, (1 - v) ^ (-(2 / 3 : ℝ)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact Real.rpow_nonneg (by linarith [hv.2]) _
  have hn := shiftedPowerBound_nonneg (1 / 4)
  positivity

theorem weakSingularity_majorant_integrable (a : ℝ) :
    IntervalIntegrable (fun v : ℝ => ‖v - a‖ ^ (-(1 / 4 : ℝ)) / 4 +
      (1 - v) ^ (-(2 / 3 : ℝ)) / (4 / 3)) volume 0 1 :=
  (IntervalIntegrable.div_const (shiftedPower_integrable (by norm_num : (1 / 4 : ℝ) < 1) a) 4).add
    (IntervalIntegrable.div_const (endpointPower_integrable (by norm_num : (2 / 3 : ℝ) < 1)) (4 / 3))

theorem weakSingularity_majorant_integral_le {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (∫ v in (0 : ℝ)..1, ‖v - a‖ ^ (-(1 / 4 : ℝ)) / 4 +
      (1 - v) ^ (-(2 / 3 : ℝ)) / (4 / 3)) ≤ weakSingularityBound := by
  rw [intervalIntegral.integral_add
    (IntervalIntegrable.div_const (shiftedPower_integrable (by norm_num : (1 / 4 : ℝ) < 1) a) 4)
    (IntervalIntegrable.div_const (endpointPower_integrable (by norm_num : (2 / 3 : ℝ) < 1)) (4 / 3)),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  unfold weakSingularityBound
  have h := shiftedPower_integral_le (by norm_num : (1 / 4 : ℝ) < 1) ha0 ha2
  linarith

end AperyMoments
