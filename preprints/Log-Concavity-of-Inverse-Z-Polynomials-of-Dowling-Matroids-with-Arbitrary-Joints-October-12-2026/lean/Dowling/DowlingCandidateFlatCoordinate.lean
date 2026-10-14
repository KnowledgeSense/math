import Dowling.DowlingCandidateCoordinateIdentities

noncomputable section
namespace Dowling
open PowerSeries

/-- The actual flat-partition substitution `(exp(m t x)-1)/(m t)`, in a
power-series form with no division by the parameter polynomial. -/
def dowlingFlatCoordinate (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  X*(PowerSeries.map Polynomial.C candidateExpTailReal).subst
    (C (Polynomial.C m)*C Polynomial.X*X)

@[simp] theorem dowlingFlatCoordinate_constantCoeff (m : ℝ) :
    (dowlingFlatCoordinate m).constantCoeff=0 := by simp [dowlingFlatCoordinate]

theorem dowlingFlatCoordinate_coeff_succ (m : ℝ) (n : ℕ) :
    coeff (n+1) (dowlingFlatCoordinate m)=
      Polynomial.C (m^n/(n+1).factorial)*Polynomial.X^n := by
  rw [dowlingFlatCoordinate,coeff_succ_X_mul,← map_mul,← smul_eq_C_mul,
    ← rescale_eq_subst,coeff_rescale,coeff_map]
  simp only [candidateExpTailReal,coeff_mk,mul_pow,map_pow,div_eq_mul_inv,map_mul]
  ring

 theorem dowlingFlatCoordinate_cleared (m : ℝ) :
    C (Polynomial.C m)*C Polynomial.X*dowlingFlatCoordinate m=
      candidateExp (C (Polynomial.C m)*C Polynomial.X*X)-1 := by
  have hz : (C (Polynomial.C m)*C Polynomial.X*(X : PowerSeries (Polynomial ℝ))).constantCoeff=0 := by simp
  have h := candidateExpTail_subst hz
  simpa only [dowlingFlatCoordinate,mul_assoc] using h

@[simp] theorem dowlingFlatCoordinate_coeff_one (m : ℝ) :
    coeff 1 (dowlingFlatCoordinate m)=1 := by
  simpa using dowlingFlatCoordinate_coeff_succ m 0

end Dowling
