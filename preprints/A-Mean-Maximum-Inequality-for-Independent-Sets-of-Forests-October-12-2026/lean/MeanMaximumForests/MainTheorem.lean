import MeanMaximumForests.ReleaseCones
import MeanMaximumForests.GraphInvariants

namespace MeanMaximumForests

/-- Every finite forest has mean independent-set size at least 47/100 of its
independence number. The mean gives equal weight to all independent sets. -/
theorem mean_maximum_inequality {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    (47 / 100 : ℝ) * G.indepNum ≤ graphMean G := by
  classical
  exact graphMean_lower_bound G Release.release_invariant hG

end MeanMaximumForests
