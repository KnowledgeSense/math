import MeanMaximumForests.PeakLimits

open MeanMaximumForests Filter
open scoped Topology

example : Tendsto forestPeakMinimum atTop (𝓝 beta) := forestPeakMinimum_tendsto
example : Tendsto treePeakMinimum atTop (𝓝 beta) := treePeakMinimum_tendsto
example : (47 / 100 : ℝ) ≤ beta ∧ beta < (473403 / 1000000 : ℝ) := weak_peak_limits.2.2

example (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      N ≤ Fintype.card V → ∀ k : ℕ, WeakLocalPeak G k →
        beta - ε < (k : ℝ) / G.indepNum := forest_weak_peaks_uniform_lower ε hε

#print axioms MeanMaximumForests.weak_peak_limits
#print axioms MeanMaximumForests.forestPeakMinimum_tendsto
#print axioms MeanMaximumForests.treePeakMinimum_tendsto
#print axioms MeanMaximumForests.PeakAnalysis.forest_integer_mass_bounds
#print axioms MeanMaximumForests.PeakAnalysis.forest_tilted_adjacent_ratio
#print axioms MeanMaximumForests.forest_weak_peaks_uniform_lower
