import MeanMaximumForests.IndependentSetLaw
import HardCoreActivityThreshold.SubcriticalGraph
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

/-- Uniform variance for every positive, possibly inhomogeneous activity bounded by one. -/
theorem forest_small_activity_variance : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      ∀ (activity : V → ℝ) (ha : ∀ v, 0 < activity v), (∀ v, activity v ≤ 1) →
        (hardCoreLaw G activity ha).variance (fun s => (s.card : ℝ)) ≤ C * Fintype.card V := by
  have hcap : (1 : ℝ) < criticalActivity :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 15.67367648339) criticalActivity_bounds.1
  obtain ⟨C, hC, hc⟩ := subcritical_graph_correlation 1 (by norm_num) hcap
  refine ⟨C / 4, by positivity, ?_⟩
  intro V _ _ G hG activity ha hact
  have hb := cardinal_variance_le_of_correlation (hardCoreLaw G activity ha) C hC.le
    (hc G hG activity ha hact) (fun v => hardCore_occupation_variance_pos G activity ha v)
  nlinarith only [hb]

end MeanMaximumForests.PeakAnalysis
