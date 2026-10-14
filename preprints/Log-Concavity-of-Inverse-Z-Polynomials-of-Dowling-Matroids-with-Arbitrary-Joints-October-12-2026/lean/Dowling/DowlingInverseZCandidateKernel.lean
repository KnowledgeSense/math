import Dowling.DowlingInverseZCandidateFactors

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingQuadraticExp_add (a b : ℝ) :
    dowlingQuadraticExp a*dowlingQuadraticExp b=dowlingQuadraticExp (a+b) := by
  rw [dowlingQuadraticExp,dowlingQuadraticExp,dowlingQuadraticExp,
    ← candidateExp_add (by simp) (by simp)]
  congr 1
  simp only [map_add]
  ring

/-- The literal source coefficient kernel, including its signed Jacobian factor. -/
def dowlingInverseZKernel (a : ℝ) (n : ℕ) : PowerSeries (Polynomial ℝ) :=
  (1-C Polynomial.X*X^2)*dowlingQuadraticExp (((n : ℝ)+a)/2)*
    dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X)

theorem dowlingInverseZCandidate_coeff_kernel (m : ℝ) (n : ℕ) :
    coeff n (dowlingInverseZCandidate m)=
      Polynomial.C (m^n)*coeff n (dowlingInverseZKernel m⁻¹ n) := by
  rw [dowlingInverseZCandidate_coefficient_change,dowlingInverseZBase_factorization,
    dowlingQuadraticExp_power]
  apply congrArg (fun p : Polynomial ℝ => Polynomial.C (m^n)*p)
  apply congrArg (coeff n)
  have h := dowlingQuadraticExp_add (m⁻¹/2) ((n : ℝ)/2)
  rw [show m⁻¹/2+(n : ℝ)/2=((n : ℝ)+m⁻¹)/2 by ring] at h
  dsimp only [dowlingInverseZKernel]
  rw [← h]
  ring

end Dowling
