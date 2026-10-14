import MeanMaximumForests.PeakAnalysis.GraphTilt
import MeanMaximumForests.CoefficientLower
import Mathlib.Topology.Order.IntermediateValue

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset Set

/-- A uniform Lipschitz estimate for the genuine forest mean in log activity below zero. -/
theorem forest_tilt_mean_gap : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      ∀ t : ℝ, t ≤ 0 → graphMean G - graphTiltMean G t ≤ C * Fintype.card V * (-t) := by
  obtain ⟨C, hC, hc⟩ := forest_small_activity_variance
  refine ⟨C, hC, ?_⟩
  intro V _ _ G hG t ht
  have hd : Differentiable ℝ (graphTiltMean G) := fun s => (graphTiltMean_hasDerivAt G s).differentiableAt
  have hb : ∀ s ∈ interior (Iic (0 : ℝ)), deriv (graphTiltMean G) s ≤ C * Fintype.card V := by
    intro s hs
    rw [(graphTiltMean_hasDerivAt G s).deriv]
    apply hc G hG
    intro v
    exact Real.exp_le_one_iff.mpr (by
      have hs0 : s < 0 := by simpa only [interior_Iic, Set.mem_Iio] using hs
      exact hs0.le)
  have h := (convex_Iic (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le hd.continuous.continuousOn
    hd.differentiableOn hb t (Set.mem_Iic.mpr ht) 0 (Set.mem_Iic.mpr le_rfl) ht
  simpa only [graphTiltMean_zero, zero_sub] using h

/-- Every weak local peak below the uniform mean is a genuine tilted mean for activity in `[1/4,1]`. -/
theorem weakLocalPeak_tilt_mean {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hn : 5 ≤ Fintype.card V)
    {k : ℕ} (hk : WeakLocalPeak G k) (hkm : (k : ℝ) ≤ graphMean G) :
    ∃ t ∈ Icc (Real.log (1 / 4)) 0, graphTiltMean G t = k := by
  have hl := weakLocalPeak_lower G hG hk
  have hl' : (Fintype.card V : ℝ) ≤ 4 * k + 1 := by exact_mod_cast hl
  have hn' : (5 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hkq : graphTiltMean G (Real.log (1 / 4)) ≤ (k : ℝ) :=
    (graphTiltMean_quarter G).trans (by linarith)
  have ht0 : Real.log (1 / 4 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hcont : Continuous (graphTiltMean G) := continuous_iff_continuousAt.mpr
    (fun t => (graphTiltMean_hasDerivAt G t).continuousAt)
  exact intermediate_value_Icc ht0 hcont.continuousOn ⟨hkq, by simpa only [graphTiltMean_zero] using hkm⟩

end MeanMaximumForests.PeakAnalysis
