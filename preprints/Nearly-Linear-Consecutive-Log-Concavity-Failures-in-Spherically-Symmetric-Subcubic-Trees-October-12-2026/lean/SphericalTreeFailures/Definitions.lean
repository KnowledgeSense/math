import SphericalTreeFailures.GraphPolynomial
import SphericalTreeFailures.GraphDegree

namespace SphericalTreeFailures
set_option backward.isDefEq.respectTransparency false

/-- The path on `n` vertices, rooted at an endpoint when nonempty. -/
def pendantPath : ℕ → ForestExpr
  | 0 => .empty
  | n + 1 => .root (pendantPath n)

/-- A complete binary core of depth `m`, with `n` new path vertices at each leaf. -/
def sphericalTree : ℕ → ℕ → ForestExpr
  | 0, n => pendantPath (n + 1)
  | m + 1, n => .root (.union (sphericalTree m n) (sphericalTree m n))

noncomputable def coefficient (m n j : ℕ) : ℕ :=
  (independencePolynomial (sphericalTree m n).graph Finset.univ).coeff j

noncomputable def independenceNumberOfTree (m n : ℕ) : ℕ :=
  (sphericalTree m n).graph.indepNum

end SphericalTreeFailures
