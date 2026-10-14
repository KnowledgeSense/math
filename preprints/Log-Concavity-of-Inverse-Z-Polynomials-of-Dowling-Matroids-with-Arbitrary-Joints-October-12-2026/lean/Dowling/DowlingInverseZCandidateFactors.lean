import Dowling.DowlingInverseZCandidateBinomial

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingInverseZBase_factorization (a : ℝ) :
    dowlingInverseZBase a = dowlingQuadraticExp (a/2)*dowlingBinomialSeries a*
      (dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) := by
  have hn : HasSubst (-X : PowerSeries (Polynomial ℝ)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have ht : PowerSeries.constantCoeff (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))=0 := by simp
  have hts := HasSubst.of_constantCoeff_zero' ht
  have hlog : PowerSeries.subst (-X : PowerSeries (Polynomial ℝ))
      (PowerSeries.subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) (log (Polynomial ℝ)))=
      PowerSeries.subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) ((log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) := by
    rw [subst_comp_subst_apply hts hn,subst_comp_subst_apply hn hts]
    congr 1
    rw [candidate_subst_C_mul_X (by simp),← coe_substAlgHom hts,map_neg,coe_substAlgHom,subst_X hts]
    ring
  have he : -C (Polynomial.C a)*candidateLogZInU.subst (-X : PowerSeries (Polynomial ℝ))=
      C (Polynomial.C (a/2))*C Polynomial.X*X^2 +
      (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) +
      PowerSeries.subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))
        (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) := by
    rw [candidateLogZInU,← coe_substAlgHom hn,map_sub,map_add]
    simp only [map_mul,map_pow,coe_substAlgHom,subst_C,subst_X hn]
    rw [hlog]
    have hs : PowerSeries.subst (C Polynomial.X*X)
        (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) =
        -C (Polynomial.C a)*PowerSeries.subst (C Polynomial.X*X)
          ((log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) := by
      rw [← coe_substAlgHom hts,map_mul,map_neg,coe_substAlgHom,subst_C]
      rfl
    rw [hs]
    change -C (Polynomial.C a)*
      ((log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ)) +
       PowerSeries.subst (C Polynomial.X*X) ((log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))) -
       C (Polynomial.C (1/2 : ℝ))*C Polynomial.X*(-X)^2)=_
    have hc : C (Polynomial.C (a/2))=
        (C (Polynomial.C a) : PowerSeries (Polynomial ℝ))*C (Polynomial.C (1/2 : ℝ)) := by
      rw [← map_mul,← Polynomial.C_mul]
      congr 2
      ring
    rw [hc]
    ring
  have ha := dowlingBinomial_argument_constantCoeff a
  have hat : PowerSeries.constantCoeff (PowerSeries.subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))
      (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ))))=0 := by
    rw [candidate_subst_constantCoeff _ _ ht,ha]
  rw [dowlingInverseZBase,he,candidateExp_add (by rw [map_add,ha]; simp) hat,
    candidateExp_add (by simp) ha,← candidateExp_subst ha ht]
  rfl

set_option maxHeartbeats 800000 in
/-- Exact Jacobian coefficient extraction before finite polynomial expansion. -/
theorem dowlingInverseZCandidate_coefficient_change (m : ℝ) (n : ℕ) :
    coeff n (dowlingInverseZCandidate m)=Polynomial.C (m^n)*
      coeff n (dowlingInverseZBase m⁻¹*
        (candidateExp (-dowlingQuadraticExponent))^n*(1-C Polynomial.X*X^2)) := by
  have hL := HasSubst.of_constantCoeff_zero' dowlingLambertInverse_constantCoeff
  have hm : HasSubst (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have he : dowlingInverseZCandidate m =
      PowerSeries.subst (C (Polynomial.C m)*X) (PowerSeries.subst dowlingLambertInverse (dowlingInverseZBase m⁻¹)) := by
    rw [dowlingInverseZCandidate,subst_comp_subst_apply hL hm]
  rw [he,← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,← Polynomial.C_pow]
  congr 1
  have h := Fan.coeff_change_variable
    ((dowlingInverseZBase m⁻¹).subst dowlingLambertInverse)
    (candidateExp dowlingQuadraticExponent) (candidateExp (-dowlingQuadraticExponent))
    (candidateExp_neg dowlingQuadraticExponent_constantCoeff) n
  change coeff n ((dowlingInverseZBase m⁻¹).subst dowlingLambertInverse) = _ at h
  rw [show X*candidateExp dowlingQuadraticExponent=dowlingLambertCoordinate from rfl,
    subst_comp_subst_apply hL (HasSubst.of_constantCoeff_zero' dowlingLambertCoordinate_constantCoeff),
    dowlingLambertInverse_subst_coordinate,X_subst,dowlingLambertCoordinate_derivative] at h
  rw [h]
  congr 1
  have hi := candidateExp_neg dowlingQuadraticExponent_constantCoeff
  rw [pow_succ]
  linear_combination dowlingInverseZBase m⁻¹*(candidateExp (-dowlingQuadraticExponent))^n*
    (1-C Polynomial.X*X^2)*hi

end Dowling
