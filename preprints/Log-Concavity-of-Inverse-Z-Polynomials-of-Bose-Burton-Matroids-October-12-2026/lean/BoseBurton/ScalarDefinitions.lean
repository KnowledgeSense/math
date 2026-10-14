import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace BoseBurton
open Finset

/-- Finite q-factorial with the source's normalization p₀=1. -/
def qFactorial (z : ℝ) (n : ℕ) : ℝ := ∏ i∈range n, (1-z^(i+1))

/-- Gaussian binomial coefficient, explicitly zero outside its support. -/
def gaussian (z : ℝ) (n k : ℕ) : ℝ :=
  if k≤n then qFactorial z n/(qFactorial z k*qFactorial z (n-k)) else 0

/-- Supported falling product. Natural subtraction retains the source's
zero factor when j reaches k. -/
def fallingProduct (z : ℝ) (j k : ℕ) : ℝ := ∏ i∈range j, (1-z^(k-(i+1)))

def pairedProduct (z : ℝ) (r j k : ℕ) : ℝ :=
  fallingProduct z j k*fallingProduct z j (r-k)

def positiveWeight (z : ℝ) (r s j : ℕ) : ℝ :=
  (1-z^(r-s))*z^(j*(r-s+j+1))*gaussian z s j*qFactorial z (r-j-1)/
    (qFactorial z r*qFactorial z j)

def endpointFactor (z : ℝ) (r s : ℕ) : ℝ := ∏ i∈range s,(1-z^(r-s+i))

def normalizedCoefficient (z : ℝ) (r s k : ℕ) : ℝ :=
  if k=0 ∨ k=r then endpointFactor z r s else
    ∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k

/-- The scalar row after removal of the common positive projective scale. -/
def scalarCoefficient (z : ℝ) (r s k : ℕ) : ℝ :=
  gaussian z r k*normalizedCoefficient z r s k

end BoseBurton
