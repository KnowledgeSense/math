import TerminalLogConcavity.Definitions
import TerminalLogConcavity.ReleaseCoefficientBounds
import TerminalLogConcavity.ReleaseIndependence

namespace TerminalLogConcavity

theorem release_reversed_coefficient {r H k : ℕ}
    (hk : k ≤ (releaseTree r H).graph.indepNum) :
    (releaseReversedPolynomial (r + 1) H).coeff k =
      independenceCoefficient (releaseTree r H).graph ((releaseTree r H).graph.indepNum - k) := by
  change (Polynomial.reflect (releaseTree r H).graph.indepNum
    (independencePolynomial (releaseTree r H).graph Finset.univ)).coeff k = _
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hk]
  exact (independenceCoefficient_eq_polynomial _ _).symm

end TerminalLogConcavity
