import Dowling.DowlingInverseZCandidateDefinitions

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingBraidZ_subst_coordinate :
    dowlingBraidZ.subst dowlingLogCoordinate =
      (1+X)*(1+C Polynomial.X*X)*candidateExp dowlingQuadraticExponent := by
  rw [dowlingBraidZ,candidateExp_subst braidLogZCandidate_constantCoeff
    dowlingLogCoordinate_constantCoeff,braidLogZCandidate_subst_coordinate]
  have hl : PowerSeries.constantCoeff (log (Polynomial ℝ))=0 := constantCoeff_log
  have htl : PowerSeries.constantCoeff
      ((log (Polynomial ℝ)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))))=0 := by
    rw [candidate_subst_constantCoeff _ _ (by simp),hl]
  have heq : candidateLogZInU = log (Polynomial ℝ) +
      (log (Polynomial ℝ)).subst (C Polynomial.X*X)+dowlingQuadraticExponent := by
    dsimp [candidateLogZInU,dowlingQuadraticExponent]
    ring
  rw [heq,candidateExp_add (by simp [hl,htl]) dowlingQuadraticExponent_constantCoeff,
    candidateExp_add hl htl,candidateExp_log_subst (by simp)]
  have hlog : candidateExp (log (Polynomial ℝ))=1+X := by
    simpa only [X_subst] using candidateExp_log_subst
      (g := (X : PowerSeries (Polynomial ℝ))) (by simp)
  rw [hlog]

theorem dowlingQuadraticExponent_derivative :
    derivative dowlingQuadraticExponent = -C Polynomial.X*X := by
  simp only [dowlingQuadraticExponent,Derivation.leibniz,map_neg,
    derivative_C,derivative_pow,derivative_X,smul_eq_mul,neg_zero,mul_zero,
    zero_add,mul_one]
  have hc : (2 : PowerSeries (Polynomial ℝ))*C (Polynomial.C (1/2 : ℝ))=1 := by
    have h := congrArg (fun r : ℝ => (C (Polynomial.C r) : PowerSeries (Polynomial ℝ)))
      (show (2 : ℝ)*(1/2)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using h
  linear_combination -C Polynomial.X*X*hc

theorem dowlingLambertCoordinate_derivative :
    derivative dowlingLambertCoordinate =
      candidateExp dowlingQuadraticExponent*(1-C Polynomial.X*X^2) := by
  have hd : derivative (X*candidateExp dowlingQuadraticExponent) =
      candidateExp dowlingQuadraticExponent + X*derivative (candidateExp dowlingQuadraticExponent) := by
    simp [Derivation.leibniz,add_comm]
  rw [dowlingLambertCoordinate,hd,derivative_candidateExp dowlingQuadraticExponent_constantCoeff,
    dowlingQuadraticExponent_derivative]
  ring

/-- The block primitive is the literal Gaussian Lambert coordinate. -/
theorem dowlingBraidPrimitive_subst_coordinate :
    dowlingBraidPrimitive.subst dowlingLogCoordinate=dowlingLambertCoordinate := by
  apply derivative.ext
  · rw [derivative_subst (HasSubst.of_constantCoeff_zero' dowlingLogCoordinate_constantCoeff),
      dowlingBraidPrimitive,derivative_candidatePrimitive,dowlingBraidZ_subst_coordinate,
      dowlingLambertCoordinate_derivative]
    linear_combination candidateExp dowlingQuadraticExponent*dowlingLogCoordinate_derivative
  · rw [candidate_subst_constantCoeff _ _ dowlingLogCoordinate_constantCoeff,
      dowlingBraidPrimitive_constantCoeff,dowlingLambertCoordinate_constantCoeff]

end Dowling
