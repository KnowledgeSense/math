import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section

namespace PowerWeights

open Polynomial

/-- The two complete exponent schedules appearing in the source. -/
inductive Schedule where
  | printed
  | example
  deriving DecidableEq

/-- Zero-based form of `(0,0,1,…,N-2)` and `(0,1,…,N-1)`. -/
def exponent (s : Schedule) (i : ℕ) : ℕ :=
  match s with
  | .printed => i-1
  | .example => i

/-- The actual alternating path matrix. Parameter `a i` is the edge joining
vertices `i` and `i+1`; parameters outside this finite path are unused. -/
def pathMatrix (N : ℕ) (a : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i.val % 2 = 0 ∧ j.val = i.val+1 then (a i.val : ℂ)
    else if i.val % 2 = 0 ∧ i.val = j.val+1 then (a j.val : ℂ) else 0

abbrev PolynomialMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ[X]

/-- Embed a constant matrix entrywise into polynomial matrices. -/
def constant {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) : PolynomialMatrix N :=
  F.map Polynomial.C

/-- Coefficientwise complex conjugation leaves the real variable unchanged. -/
def conjugate (p : ℂ[X]) : ℂ[X] := p.map (starRingEnd ℂ)

/-- The adjoint of a polynomial matrix with a real formal variable. -/
def adjoint {N : ℕ} (P : PolynomialMatrix N) : PolynomialMatrix N :=
  fun i j => conjugate (P j i)

/-- `T(x)=I+xA`, the source's degree-one matrix factor. -/
def factor (N : ℕ) (a : ℕ → ℝ) : PolynomialMatrix N :=
  1 + (Polynomial.X : ℂ[X]) • constant (pathMatrix N a)

/-- The diagonal scalar-power factor for either source convention. -/
def diagonal (N : ℕ) (s : Schedule) : PolynomialMatrix N :=
  Matrix.diagonal fun i => (Polynomial.X : ℂ[X]) ^ exponent s i.val

/-- The actual polynomial part of the matrix weight. -/
def polynomialWeight (N : ℕ) (s : Schedule) (a : ℕ → ℝ) : PolynomialMatrix N :=
  factor N a * diagonal N s * adjoint (factor N a)

/-- Evaluate the original matrix weight on the real line. -/
def weight (N : ℕ) (s : Schedule) (a : ℕ → ℝ) (w : ℝ → ℝ) (x : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (w x : ℂ) • (polynomialWeight N s a).map (Polynomial.eval (x : ℂ))

end PowerWeights
