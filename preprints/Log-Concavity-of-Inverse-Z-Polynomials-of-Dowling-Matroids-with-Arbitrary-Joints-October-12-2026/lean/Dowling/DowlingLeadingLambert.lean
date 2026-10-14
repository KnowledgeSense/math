import Dowling.DowlingLeadingExponential

noncomputable section
namespace Dowling
open PowerSeries

def dowlingQuadraticExponent : PowerSeries (Polynomial ℝ) :=
  -C Polynomial.X*C (Polynomial.C (1/2 : ℝ))*X^2

def dowlingLambertCoordinate : PowerSeries (Polynomial ℝ) :=
  X*candidateExp dowlingQuadraticExponent

 theorem candidateH_quadratic_weight :
    CandidateWeight 3 (candidateH-C (Polynomial.C (1/2 : ℝ))*X^2) := by
  have h := candidateWeight_realSeries (w := 3)
    (candidateHReal-C (1/2 : ℝ)*X^2) (by
      intro n hn
      interval_cases n <;> norm_num [candidateHReal,coeff_C_mul,coeff_X_pow,coeff_exp,coeff_X])
  simpa only [map_sub,map_mul,map_C,map_pow,map_X,candidateH] using h

 theorem dowlingQuadraticExponent_weight : CandidateWeight 0 dowlingQuadraticExponent := by
  have h : CandidateWeight 2 (C (Polynomial.C (1/2 : ℝ))*(X : PowerSeries (Polynomial ℝ))^2) := by
    simpa using (candidateWeight_X.pow 2).scalar_mul (1/2)
  simpa only [dowlingQuadraticExponent,mul_assoc,neg_mul] using h.parameter_mul.neg

@[simp] theorem dowlingQuadraticExponent_constantCoeff : dowlingQuadraticExponent.constantCoeff=0 := by
  simp [dowlingQuadraticExponent]

 theorem dowlingLambertCoordinate_weight : CandidateWeight 1 dowlingLambertCoordinate := by
  simpa only [dowlingLambertCoordinate,candidateExp,add_zero] using candidateWeight_X.mul
    (dowlingQuadraticExponent_weight.exp dowlingQuadraticExponent_constantCoeff)

@[simp] theorem dowlingLambertCoordinate_constantCoeff : dowlingLambertCoordinate.constantCoeff=0 :=
  dowlingLambertCoordinate_weight.constantCoeff_eq_zero (by omega)

@[simp] theorem dowlingLambertCoordinate_coeff_one : coeff 1 dowlingLambertCoordinate=1 := by
  rw [dowlingLambertCoordinate,coeff_succ_X_mul,coeff_zero_eq_constantCoeff_apply,
    candidateExp_constantCoeff dowlingQuadraticExponent_constantCoeff]

 theorem dowlingVCoordinate_lambert_difference :
    CandidateWeight 2 (dowlingVCoordinate-dowlingLambertCoordinate) := by
  have harg : CandidateWeight 1 (candidateNegativeTH-dowlingQuadraticExponent) := by
    have h := candidateH_quadratic_weight.parameter_mul.neg
    convert h using 1
    dsimp [candidateNegativeTH,dowlingQuadraticExponent]
    ring
  have hexp := candidateWeight_exp_difference candidateNegativeTH_weight
    dowlingQuadraticExponent_weight candidateNegativeTH_constantCoeff
    dowlingQuadraticExponent_constantCoeff harg
  have hE := candidateNegativeTH_weight.exp candidateNegativeTH_constantCoeff
  have hT := candidateWeight_realSeries_subst (v := 0) candidateExpTailReal
    (by intro d hd; omega) candidateNegativeTH_weight candidateNegativeTH_constantCoeff
  have hfirst : CandidateWeight 2 (candidateH*candidateExp candidateNegativeTH) := by
    simpa only [candidateExp,add_zero] using candidateH_weight.mul hE
  have hsecond : CandidateWeight 2 (X*(candidateExp candidateNegativeTH-
      candidateExp dowlingQuadraticExponent)) := candidateWeight_X.mul hexp
  have hthird : CandidateWeight 2 (candidateH*
      (PowerSeries.map Polynomial.C candidateExpTailReal).subst candidateNegativeTH) := by
    simpa using candidateH_weight.mul hT
  have h := (hfirst.add hsecond).sub hthird
  convert h using 1
  dsimp [dowlingVCoordinate,dowlingLambertCoordinate,candidateExp]
  simp only [candidateH_eq]
  ring

/-- The Lambert inverse captures all weight-one coefficients of the KL coordinate. -/
def dowlingLambertInverse : PowerSeries (Polynomial ℝ) :=
  dowlingLambertCoordinate.substInvOfIsUnit (by simp)

theorem dowlingLambertInverse_weight : CandidateWeight 1 dowlingLambertInverse :=
  dowlingLambertCoordinate_weight.substInvOfIsUnit dowlingLambertCoordinate_coeff_one _

theorem dowlingVInverse_lambert_difference :
    CandidateWeight 2 (dowlingVInverse-dowlingLambertInverse) :=
  candidateWeight_inverse_difference dowlingVCoordinate_weight dowlingLambertCoordinate_weight
    dowlingVCoordinate_coeff_one dowlingLambertCoordinate_coeff_one dowlingVCoordinate_lambert_difference

end Dowling
