import MeanMaximumForests.IndependentSetLaw
import HardCoreActivityThreshold.SubcriticalGraph
set_option maxHeartbeats 500000
namespace MeanMaximumForests
universe u
open HardCoreActivityThreshold
/-- Uniform linear variance for all finite forests, with no degree restriction. -/
theorem forest_variance_linear : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      graphVariance G ≤ C * Fintype.card V := by
  have hcap : (1 : ℝ) < criticalActivity :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 15.67367648339) criticalActivity_bounds.1
  refine Exists.elim (subcritical_graph_correlation.{u} 1 (by norm_num) hcap) ?_
  intro C hCinfo
  rcases hCinfo with ⟨hC, hc⟩
  refine ⟨C / 4, by positivity, ?_⟩
  intro V _ _ G hG
  have hc1 : CorrelationBound (uniformIndependentSetLaw G) C := by
    unfold uniformIndependentSetLaw
    apply hc G hG
    intro v
    exact le_rfl
  have hv1 : ∀ v, 0 < occupationVariance (uniformIndependentSetLaw G) v := by
    intro v
    exact hardCore_occupation_variance_pos G (fun _ => 1) (fun _ => by norm_num) v
  have hb := cardinal_variance_le_of_correlation (uniformIndependentSetLaw G) C hC.le hc1 hv1
  rw [uniformIndependentSetLaw_variance] at hb
  nlinarith

end MeanMaximumForests
