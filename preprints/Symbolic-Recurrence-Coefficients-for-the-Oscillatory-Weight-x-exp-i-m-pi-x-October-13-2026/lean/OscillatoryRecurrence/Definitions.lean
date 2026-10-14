import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Polynomial
namespace OscillatoryRecurrence

/-- Bilinear moments on the real interval; no complex conjugation is used. -/
def exponentialMoment (t : ℂ) (k : ℕ) : ℂ :=
  ∫ x : ℝ in (-1)..1, (x : ℂ)^k * Complex.exp (t*x)

def moment (η : ℝ) (r : ℕ) : ℂ := exponentialMoment (Complex.I*η) (r+1)

def hankel (η : ℝ) (n : ℕ) : ℂ :=
  Matrix.det (fun a b : Fin n => moment η (a.val+b.val))

def borderColumn (n : ℕ) (b : Fin n) : ℕ := if b.val+1=n then n else b.val

def borderedHankel (η : ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else Matrix.det (fun a b : Fin n => moment η (a.val+borderColumn n b))

/-- Polynomial endpoint recurrence, with coefficients in the rational field. -/
def endpointMoment : ℕ → ℚ[X]
  | 0 => 2
  | r+1 => Polynomial.C ((r+2 : ℕ) : ℚ) * endpointMoment r +
      Polynomial.C (if Even (r+1) then 2*(-1 : ℚ)^((r+1)/2) else 0) * Polynomial.X^((r+1)/2)

def polynomialHankel (n : ℕ) : ℚ[X] :=
  Matrix.det (fun a b : Fin n => endpointMoment (a.val+b.val))

def polynomialBorder (n : ℕ) : ℚ[X] :=
  if n=0 then 0 else Matrix.det (fun a b : Fin n => endpointMoment (a.val+borderColumn n b))

end OscillatoryRecurrence
