import AperyMoments.CorrectionKernel

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def convolutionEndpointWeight (v : ℝ) : ℝ :=
  v ^ (-(1 / 8 : ℝ)) * (1 - v) ^ (-(1 / 2 : ℝ))

theorem convolutionEndpointWeight_integrable :
    IntervalIntegrable convolutionEndpointWeight volume 0 1 := by
  have hf : IntervalIntegrable (fun v : ℝ => v ^ (-(1 / 8 : ℝ))) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hg : ContinuousOn (fun v : ℝ => (1 - v) ^ (-(1 / 2 : ℝ))) (Icc 0 (1 / 2)) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro v hv
    left
    linarith [hv.2]
  have hi : IntervalIntegrable convolutionEndpointWeight volume 0 (1 / 2) := by
    apply hf.mul_continuousOn
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hg
  have hj : IntervalIntegrable (fun v : ℝ => (1 - v) ^ (-(1 / 2 : ℝ))) volume (1 / 2) 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1 / 2)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left 1
    norm_num at h
    exact h.symm
  have hk : ContinuousOn (fun v : ℝ => v ^ (-(1 / 8 : ℝ))) (Icc (1 / 2) 1) := by
    apply continuousOn_id.rpow_const
    intro v hv
    left
    change v ≠ 0
    linarith [hv.1]
  have hl : IntervalIntegrable convolutionEndpointWeight volume (1 / 2) 1 := by
    apply hj.continuousOn_mul
    simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hk
  exact hi.trans hl

end AperyMoments
