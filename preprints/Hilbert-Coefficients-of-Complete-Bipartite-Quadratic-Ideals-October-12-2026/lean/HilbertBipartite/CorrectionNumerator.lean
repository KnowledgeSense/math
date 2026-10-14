import HilbertBipartite.CoefficientConvolution
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations

open Finset Polynomial
namespace HilbertBipartite

/-- The polynomial `P_{a,b}` in equation (P), with every indexing set explicitly finite. -/
noncomputable def correctionPolynomial (a b : ℕ) : Polynomial ℚ :=
  ∑ t ∈ range (a+1), ∑ r ∈ Icc 1 a, ∑ k ∈ Icc (t+2*r) a,
    C (((t+b-1).choose (b-1) : ℚ) * (a.choose k : ℚ)) * X^(t+r-1)

end HilbertBipartite
