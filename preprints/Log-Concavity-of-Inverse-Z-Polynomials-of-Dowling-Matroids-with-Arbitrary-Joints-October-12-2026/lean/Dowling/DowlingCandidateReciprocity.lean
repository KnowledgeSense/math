import Dowling.DowlingCandidateInverseReciprocity

noncomputable section
namespace Dowling
open PowerSeries

 theorem candidateEval_braid_derivative (t : ℝ) :
    derivative (candidateEval t braidLogZCandidate)=
      1+C t+C t*candidateEval t dowlingLogInverse := by
  rw [← candidateEval_derivative,braidLogZCandidate_derivative]
  simp only [map_add,map_one,map_mul,candidateEval_C,Polynomial.eval_X]

 theorem candidateEval_braid_reciprocal (t : ℝ) (ht : t≠0) :
    (candidateEval t⁻¹ braidLogZCandidate).subst (C t*X)=candidateEval t braidLogZCandidate := by
  have hs : HasSubst (C t*(X : PowerSeries ℝ)) := HasSubst.of_constantCoeff_zero' (by simp)
  apply derivative.ext
  · rw [derivative_subst hs,candidateEval_braid_derivative,candidateEval_braid_derivative]
    have hdt : derivative (C t*(X : PowerSeries ℝ))=C t := by simp
    rw [hdt,← coe_substAlgHom hs,map_add,map_add,map_one,map_mul]
    simp only [coe_substAlgHom,subst_C,candidateEval_logInverse_reciprocal t ht]
    change (1+C t⁻¹+C t⁻¹*(C t*candidateEval t dowlingLogInverse))*C t=
      1+C t+C t*candidateEval t dowlingLogInverse
    have hi : (C t : PowerSeries ℝ)*C t⁻¹=1 := by rw [← map_mul,mul_inv_cancel₀ ht,map_one]
    linear_combination (1+C t*candidateEval t dowlingLogInverse)*hi
  · rw [candidate_real_subst_constantCoeff _ _ (by simp)]
    simp only [candidateEval_constantCoeff,braidLogZCandidate_constantCoeff,Polynomial.eval_zero]

 theorem candidateEval_Z (m t : ℝ) : candidateEval t (dowlingZCandidate m)=
    candidateExp (C m⁻¹*(candidateEval t braidLogZCandidate).subst (C m*X)) := by
  have hz : (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))).constantCoeff=0 := by simp
  have hb : PowerSeries.constantCoeff (braidLogZCandidate.subst (C (Polynomial.C m)*X))=0 := by
    rw [candidate_subst_constantCoeff _ _ hz]
    exact braidLogZCandidate_constantCoeff
  change candidateEval t (candidateExp (C (Polynomial.C m⁻¹)*
      braidLogZCandidate.subst (C (Polynomial.C m)*X)))=_
  rw [candidateEval_exp _ _ (by simp [hb])]
  simp only [map_mul,candidateEval_C,Polynomial.eval_C,candidateEval_subst t _ _ hz,candidateEval_X]

 theorem candidate_real_rescale_commute (f : PowerSeries ℝ) (a b : ℝ) :
    PowerSeries.subst (C b*X) (f.subst (C a*X))=
      PowerSeries.subst (C a*X) (f.subst (C b*X)) := by
  rw [candidate_real_subst_rescale _ (by simp),candidate_real_subst_rescale _ (by simp)]
  congr 1
  ring

 theorem dowlingZCandidate_eval_reciprocal_series (m t : ℝ) (ht : t≠0) :
    (candidateEval t⁻¹ (dowlingZCandidate m)).subst (C t*X)=
      candidateEval t (dowlingZCandidate m) := by
  rw [candidateEval_Z,candidateEval_Z]
  have hc : PowerSeries.constantCoeff
      ((candidateEval t⁻¹ braidLogZCandidate).subst (C m*(X : PowerSeries ℝ)))=0 := by
    rw [candidate_real_subst_constantCoeff _ _ (by simp)]
    simp only [candidateEval_constantCoeff,
      braidLogZCandidate_constantCoeff,Polynomial.eval_zero]
  rw [candidateExp_subst (by simp [hc]) (by simp),candidate_real_subst_C_mul (by simp),
    candidate_real_rescale_commute,candidateEval_braid_reciprocal t ht]

/-- Pointwise ordinary rank reciprocity, sufficient for the strict-half-degree
uniqueness characterization of the genuine invariant. -/
theorem dowlingZCandidate_eval_reciprocal (m t : ℝ) (ht : t≠0) (n : ℕ) :
    t^n*(coeff n (dowlingZCandidate m)).eval t⁻¹=
      (coeff n (dowlingZCandidate m)).eval t := by
  have h := congrArg (coeff n) (dowlingZCandidate_eval_reciprocal_series m t ht)
  rw [← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,
    candidateEval_coeff,candidateEval_coeff] at h
  exact h

end Dowling
