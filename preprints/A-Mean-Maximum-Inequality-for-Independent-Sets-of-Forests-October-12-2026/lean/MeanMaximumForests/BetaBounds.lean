import MeanMaximumForests.MainTheorem
import MeanMaximumForests.TreeInfimum

namespace MeanMaximumForests

/-- Numerical bounds on the infimum over nonempty finite trees.
This statement does not assert convergence of peak positions. -/
theorem beta_bounds : (47 / 100 : ℝ) ≤ beta ∧ beta < (473403 / 1000000 : ℝ) :=
  ⟨beta_lower_bound Release.release_invariant, beta_lt⟩

end MeanMaximumForests
