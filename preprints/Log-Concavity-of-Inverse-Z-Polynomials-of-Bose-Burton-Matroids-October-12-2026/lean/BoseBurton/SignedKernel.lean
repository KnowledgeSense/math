import BoseBurton.ScalarDefinitions
import Mathlib.Algebra.Polynomial.Coeff

noncomputable section
namespace BoseBurton
open Finset Polynomial

/-- Projective Gaussian row with reciprocal parameter. -/
def gaussianRow (z : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k∈range (n+1),C (gaussian z n k)*X^k

/-- Both orientations, with the diagonal counted once. -/
def orientationPolynomial (h l : ℕ) : Polynomial ℝ :=
  if l<h then X^l+X^h else X^h

/-- The literal source kernel after division by q^(r choose 2), z=1/q. -/
def signedKernel (z : ℝ) (r s : ℕ) : Polynomial ℝ :=
  gaussianRow z r+
    ∑ h∈Icc 1 s,∑ l∈range (min h (r-h)+1),
      C ((-1:ℝ)^(h+l)*z^(h*(r-s)+h.choose 2+l.choose 2)*
        gaussian z s h*gaussian z (r-h) l)*
      orientationPolynomial h l*gaussianRow z (r-h-l)

end BoseBurton
