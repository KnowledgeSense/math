import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

noncomputable section
open Complex MeasureTheory
namespace CircleKernel

/-- The original chord-distance logarithmic-Laplacian, parametrized by arclength
from the base point on the unit circle. -/
def circleOperator (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  ∫ θ:ℝ in 0..2*Real.pi, (f z-f (z*Complex.exp (Complex.I*θ)))/
    (‖z-z*Complex.exp (Complex.I*θ)‖:ℂ)

/-- The literal positive-frequency eigenvalue of the circle operator. -/
def circleEigenvalue (n : ℕ) : ℝ := 4*∑j∈Finset.range n,1/(2*(j:ℝ)+1)

/-- The actual diagonal spectral series, initially in the half-plane Re(t)>1/2. -/
def diagonalSpectralKernel (t : ℂ) : ℂ :=
  1/(2*Real.pi)+(1/Real.pi)*∑'n:ℕ,Complex.exp (-(circleEigenvalue (n+1):ℂ)*t)

@[simp] theorem circleEigenvalue_zero : circleEigenvalue 0=0 := by simp [circleEigenvalue]

theorem circleEigenvalue_succ (n : ℕ) :
    circleEigenvalue (n+1)=circleEigenvalue n+4/(2*(n:ℝ)+1) := by
  rw [circleEigenvalue,Finset.sum_range_succ,circleEigenvalue]
  ring

end CircleKernel
