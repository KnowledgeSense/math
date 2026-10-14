import TerminalLogConcavity.ReleaseModel
import TerminalLogConcavity.ReleaseLower

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def releaseReversedPolynomial (q H : ℕ) : ℕ[X] :=
  Polynomial.reflect (releaseForest q (thresholdIndex (target q H))).graph.indepNum
    (independencePolynomial (releaseForest q (thresholdIndex (target q H))).graph Finset.univ)

theorem release_coefficient_lower {q H j : ℕ} (hq : 2 ≤ q) (hj : j ≤ q) :
    releaseModel q H j ≤ ((releaseReversedPolynomial q H).coeff j : ℝ) := by
  have h := scaledGaussian_le_graph hq (thresholdIndex (target q H))
  change CoeffLE (releaseModelPolynomial q H) (releaseReversedPolynomial q H) at h
  exact (releaseModelPolynomial_lower hj).trans (by exact_mod_cast h j)

end TerminalLogConcavity
