import HardCoreActivityThreshold.ScalarDerivativeEstimates
import Mathlib.Analysis.Convex.Deriv

namespace HardCoreActivityThreshold

theorem firstFivefoldDerivative_strictMonoOn :
    StrictMonoOn firstFivefoldDerivative (Set.Icc 0.5 0.62) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0.5 0.62)
  · intro x hx
    exact (firstFivefoldDerivative_hasDerivAt x (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hi := interior_subset hx
    rw [(firstFivefoldDerivative_hasDerivAt x (by linarith [hi.1])).deriv]
    exact secondFivefoldDerivative_pos x hi

theorem fivefoldGap_convexOn : ConvexOn ℝ (Set.Icc 0.5 0.62) fivefoldGap := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0.5 0.62)
  · intro x hx
    exact (fivefoldGap_hasDerivAt x (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hi := interior_subset hx
    exact (fivefoldGap_hasDerivAt x (by linarith [hi.1])).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hix := interior_subset hx
    have hiy := interior_subset hy
    rw [(fivefoldGap_hasDerivAt x (by linarith [hix.1])).deriv,
      (fivefoldGap_hasDerivAt y (by linarith [hiy.1])).deriv]
    exact firstFivefoldDerivative_strictMonoOn.monotoneOn hix hiy hxy

theorem fivefoldGap_nonneg (x : ℝ) (hx : x∈Set.Icc 0.5 0.62) : 0≤fivefoldGap x := by
  have hi : criticalLog∈interior (Set.Icc (0.5 : ℝ) 0.62) := by
    rw [interior_Icc]
    constructor <;> linarith [criticalLog_bounds.1,criticalLog_bounds.2]
  have hd : derivWithin fivefoldGap (Set.Ioi criticalLog) criticalLog=0 :=
    fivefoldGap_stationary.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi criticalLog)
  have hm := fivefoldGap_convexOn.isMinOn_of_rightDeriv_eq_zero hi hd
  have h := hm hx
  simpa [fivefoldGap_at_criticalLog] using h

end HardCoreActivityThreshold
