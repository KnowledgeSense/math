import TerminalLogConcavity.GraphPolynomial

namespace TerminalLogConcavity

/-- The number of independent vertex sets of cardinality `k` in a finite graph. -/
noncomputable def independenceCoefficient {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact ((independentSetsWithin G Finset.univ).filter (fun s => s.card = k)).card

theorem independenceCoefficient_eq_polynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    independenceCoefficient G k = (independencePolynomial G Finset.univ).coeff k := by
  classical
  exact (independencePolynomial_coeff G Finset.univ k).symm

end TerminalLogConcavity
