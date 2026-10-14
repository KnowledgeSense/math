import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ReciprocalQGamma

def qProduct (q a : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (1 - a * q ^ j)
def qInfiniteProduct (q a : ℝ) : ℝ := ∏' j : ℕ, (1 - a * q ^ j)

/-- The standard real q-gamma definition for 0 < q < 1 and positive argument. -/
def qGamma (q z : ℝ) : ℝ :=
  (1 - q) ^ (1 - z) * qInfiniteProduct q q / qInfiniteProduct q (q ^ z)

def nestedProduct (q s : ℝ) (k : ℕ) : ℝ := qProduct q (1 - s) k

end ReciprocalQGamma
