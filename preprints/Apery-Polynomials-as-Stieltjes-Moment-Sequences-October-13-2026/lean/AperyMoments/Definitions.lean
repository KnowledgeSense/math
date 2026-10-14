import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace AperyMoments

/-- The original Apéry polynomial, with its parameter in ascending powers. -/
def aperyPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * (n + j).choose j) ^ 2 * x ^ j

/-- The reciprocal polynomial obtained by reversing the original finite sum. -/
def reciprocalPolynomial (n : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * (2 * n - k).choose n) ^ 2 * α ^ k

/-- One probability measure represents every original moment and has compact nonnegative support. -/
def HasPositiveMomentRepresentation (x : ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∃ R : ℝ, 0 ≤ R ∧
    μ (Icc 0 R)ᶜ = 0 ∧ ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ ∧
      (∫ t : ℝ, t ^ n ∂μ) = aperyPolynomial n x

end AperyMoments
