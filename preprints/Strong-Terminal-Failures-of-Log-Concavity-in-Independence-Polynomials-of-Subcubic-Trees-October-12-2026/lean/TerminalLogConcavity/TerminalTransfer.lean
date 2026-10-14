import TerminalLogConcavity.ModelCoefficients
import TerminalLogConcavity.BlockSum

namespace TerminalLogConcavity

/-- The comparison coefficients of the release, with all parameters substituted. -/
noncomputable def releaseModel (q H j : ℕ) : ℝ :=
  modelCoefficient q (2 * (2 * q ^ 2) * q * (q - 1) + squareSum q)
    (2 * (4 * q ^ 2)) (selectedAmplifier q H) j

theorem releaseModel_pos {q H j : ℕ} (hj : j ≤ q) : 0 < releaseModel q H j := by
  apply modelCoefficient_pos _ hj
  exact_mod_cast amplifier_pos (thresholdIndex (target q H))

theorem terminal_failure_from_coefficient_estimates {q H : ℕ}
    (hq : 2 ≤ q) (hH : 1 ≤ H) (c : ℕ → ℕ)
    (hlower : ∀ j ≤ q, releaseModel q H j ≤ (c j : ℝ))
    (hupper : ∀ j ≤ q, (c j : ℝ) ≤ (2 : ℝ) ^ (q + 3) * releaseModel q H j)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j < q) :
    H * c j ^ 2 < c (j - 1) * c (j + 1) := by
  have hlowm := hlower (j - 1) (by omega)
  have hlowp := hlower (j + 1) (by omega)
  have h := strict_failure_of_release_bounds (by omega : 1 ≤ q) hH
    (by positivity : 0 ≤ (c j : ℝ))
    (le_of_lt (releaseModel_pos (q := q) (H := H) (j := j - 1) (by omega)))
    (releaseModel_pos (q := q) (H := H) (j := j) (by omega))
    (le_of_lt (releaseModel_pos (q := q) (H := H) (j := j + 1) (by omega)))
    hlowm hlowp (hupper j (by omega))
    (modelCoefficient_curvature (a := (selectedAmplifier q H : ℝ)) hj hjq)
  exact_mod_cast h

end TerminalLogConcavity
