import MeanMaximumForests.PeakUpperLimit
import MeanMaximumForests.BetaBounds
import MeanMaximumForests.CentralPeakReduction

open MeanMaximumForests

example : ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), G.IsAcyclic → graphVariance G ≤ C * Fintype.card V :=
  forest_variance_linear

example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, treePeakMinimum n < beta + ε :=
  treePeakMinimum_eventually_lt ε hε

example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, forestPeakMinimum n < beta + ε :=
  forestPeakMinimum_eventually_lt ε hε

#print axioms MeanMaximumForests.forest_variance_linear
#print axioms MeanMaximumForests.forest_global_modes_uniform_ratio
#print axioms MeanMaximumForests.treePeakMinimum_eventually_lt
#print axioms MeanMaximumForests.forestPeakMinimum_eventually_lt
#print axioms MeanMaximumForests.exists_all_order_tree_approximation

#print axioms MeanMaximumForests.coefficient_extension_lower
#print axioms MeanMaximumForests.weakLocalPeak_global_of_central_logConcavity
