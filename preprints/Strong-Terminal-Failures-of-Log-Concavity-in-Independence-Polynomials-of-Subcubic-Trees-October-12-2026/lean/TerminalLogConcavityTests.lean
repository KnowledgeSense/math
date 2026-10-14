import TerminalLogConcavity
import TerminalLogConcavityTests.GraphSemantics

#print axioms TerminalLogConcavity.amplifier_growth
#print axioms TerminalLogConcavity.threshold_amplifier_le_square
#print axioms TerminalLogConcavity.strict_failure_of_release_bounds

example : TerminalLogConcavity.amplifier 4 = 458329 := by decide
#print axioms TerminalLogConcavity.modelCoefficient_curvature
#print axioms TerminalLogConcavity.finite_envelope_bound
#print axioms TerminalLogConcavity.order_bound_from_count_identity
#print axioms TerminalLogConcavity.releaseTree_geometry
#print axioms TerminalLogConcavity.Block.node_envelope
#print axioms TerminalLogConcavity.Block.scaled_d_upper_exp
#print axioms TerminalLogConcavity.releaseModelPolynomial_lower
#print axioms TerminalLogConcavity.positive_composition_square_gap
#print axioms TerminalLogConcavity.release_two_sided
#print axioms TerminalLogConcavity.release_terminal_failure
#print axioms TerminalLogConcavity.strong_terminal_failures

example (r H : ℕ) (hr : 1 ≤ r) (hH : 1 ≤ H) :=
  TerminalLogConcavity.strong_terminal_failures hr hH
