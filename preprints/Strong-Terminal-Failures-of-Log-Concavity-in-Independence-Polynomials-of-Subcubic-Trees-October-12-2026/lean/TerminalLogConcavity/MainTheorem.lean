import TerminalLogConcavity.ReleaseUpper
import TerminalLogConcavity.ReleaseCoefficients
import TerminalLogConcavity.ReleaseGeometry

namespace TerminalLogConcavity

/-- The two-sided coefficient estimate for the explicit release construction. -/
theorem release_two_sided {q H j : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) (hj : j ≤ q) :
    releaseModel q H j ≤ ((releaseReversedPolynomial q H).coeff j : ℝ) ∧
    ((releaseReversedPolynomial q H).coeff j : ℝ) ≤
      (2 : ℝ) ^ (q + 3) * releaseModel q H j :=
  ⟨release_coefficient_lower hq hj, release_coefficient_upper hq hH hj⟩

/-- Every requested terminal position fails log-concavity by the prescribed factor. -/
theorem release_terminal_failure {r H j : ℕ} (hr : 1 ≤ r) (hH : 1 ≤ H)
    (hj : 1 ≤ j) (hjr : j ≤ r) :
    H * independenceCoefficient (releaseTree r H).graph
      ((releaseTree r H).graph.indepNum - j) ^ 2 <
    independenceCoefficient (releaseTree r H).graph
      ((releaseTree r H).graph.indepNum - j - 1) *
    independenceCoefficient (releaseTree r H).graph
      ((releaseTree r H).graph.indepNum - j + 1) := by
  have ha := releaseTree_independence_ge hr H
  have h := terminal_failure_from_coefficient_estimates (by omega : 2 ≤ r + 1) hH
    (releaseReversedPolynomial (r + 1) H).coeff
    (fun _ hk => release_coefficient_lower (by omega) hk)
    (fun _ hk => release_coefficient_upper (by omega) hH hk) hj (by omega)
  rw [release_reversed_coefficient (by omega : j ≤ (releaseTree r H).graph.indepNum),
    release_reversed_coefficient (by omega : j - 1 ≤ (releaseTree r H).graph.indepNum),
    release_reversed_coefficient (by omega : j + 1 ≤ (releaseTree r H).graph.indepNum)] at h
  have hm : (releaseTree r H).graph.indepNum - (j - 1) =
      (releaseTree r H).graph.indepNum - j + 1 := by omega
  have hp : (releaseTree r H).graph.indepNum - (j + 1) =
      (releaseTree r H).graph.indepNum - j - 1 := by omega
  simpa [hm, hp, Nat.mul_comm] using h

/-- The main theorem, with the explicit finite subcubic tree and the release's size bound. -/
theorem strong_terminal_failures {r H : ℕ} (hr : 1 ≤ r) (hH : 1 ≤ H) :
    (releaseTree r H).graph.IsTree ∧
    (∀ v, ((releaseTree r H).graph.neighborSet v).ncard ≤ 3) ∧
    Fintype.card (releaseTree r H).Vertex ≤
      1200 * (r + 1) ^ 4 * (r + 1 + logarithmicParameter H) ∧
    ∀ j, 1 ≤ j → j ≤ r →
      H * independenceCoefficient (releaseTree r H).graph
        ((releaseTree r H).graph.indepNum - j) ^ 2 <
      independenceCoefficient (releaseTree r H).graph
        ((releaseTree r H).graph.indepNum - j - 1) *
      independenceCoefficient (releaseTree r H).graph
        ((releaseTree r H).graph.indepNum - j + 1) :=
  ⟨releaseTree_isTree r H, releaseTree_subcubic r H, releaseTree_order hr hH,
    fun _ hj hjr => release_terminal_failure hr hH hj hjr⟩

end TerminalLogConcavity
