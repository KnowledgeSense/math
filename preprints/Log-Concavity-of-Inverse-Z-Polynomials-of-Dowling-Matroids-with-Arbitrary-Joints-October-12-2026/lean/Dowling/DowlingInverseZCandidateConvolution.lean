import Dowling.DowlingInverseZCandidateCoordinate

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingZCandidate_subst_inverseComparison (m : ℝ) (hm : m≠0) :
    (dowlingZCandidate m).subst (dowlingInverseComparison m)=
      candidateExp (C (Polynomial.C m⁻¹)*candidateLogZInU.subst (-X)) := by
  have hq := dowlingInverseComparison_constantCoeff m
  have hn : HasSubst (-X : PowerSeries (Polynomial ℝ)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  change (candidateExp (C (Polynomial.C m⁻¹)*
    braidLogZCandidate.subst (C (Polynomial.C m)*X))).subst _ = _
  rw [candidateExp_subst (by rw [map_mul,candidate_subst_constantCoeff _ _ (by simp),
    braidLogZCandidate_constantCoeff,mul_zero]) hq,
    candidate_subst_C_mul hq,candidate_subst_rescale _ hq,
    dowlingInverseComparison_cancel m hm,
    ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' dowlingLogCoordinate_constantCoeff) hn,
    braidLogZCandidate_subst_coordinate]

theorem dowlingInverseZCandidate_subst_scaled_lambert (m : ℝ) (hm : m≠0) :
    (dowlingInverseZCandidate m).subst
      (C (Polynomial.C m⁻¹)*dowlingLambertCoordinate)=dowlingInverseZBase m⁻¹ := by
  have hz : PowerSeries.constantCoeff
      (C (Polynomial.C m⁻¹)*dowlingLambertCoordinate)=0 := by simp
  rw [dowlingInverseZCandidate,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by
      rw [candidate_subst_constantCoeff _ _ (by simp),dowlingLambertInverse_constantCoeff]))
      (HasSubst.of_constantCoeff_zero' hz),candidate_subst_rescale _ hz]
  have he : C (Polynomial.C m)*(C (Polynomial.C m⁻¹)*dowlingLambertCoordinate)=
      dowlingLambertCoordinate := by rw [← mul_assoc,candidate_scalar_inverse m hm,one_mul]
  rw [he,dowlingLambertInverse_subst_coordinate,X_subst]

/-- Exact formal flat convolution, with the source sign on inverse-Z. -/
theorem dowlingInverseZCandidate_convolution (m : ℝ) (hm : m≠0) :
    dowlingZCandidate m*(dowlingInverseZCandidate m).subst (-dowlingBlockCoordinate m)=1 := by
  have hq := dowlingInverseComparison_constantCoeff m
  have hqs := HasSubst.of_constantCoeff_zero' hq
  apply candidate_subst_injective hq (dowlingInverseComparison_linear_unit m hm)
  dsimp only
  rw [← coe_substAlgHom hqs,map_mul,map_one,coe_substAlgHom,
    dowlingZCandidate_subst_inverseComparison m hm,
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp)) hqs]
  have hb : PowerSeries.subst (dowlingInverseComparison m) (-dowlingBlockCoordinate m)=
      C (Polynomial.C m⁻¹)*dowlingLambertCoordinate := by
    rw [← coe_substAlgHom hqs,map_neg,coe_substAlgHom,
      dowlingBlockCoordinate_subst_comparison m hm]
    ring
  rw [hb,dowlingInverseZCandidate_subst_scaled_lambert m hm,dowlingInverseZBase]
  have hz : PowerSeries.constantCoeff
      (C (Polynomial.C m⁻¹)*candidateLogZInU.subst (-X))=0 := by
    rw [map_mul,candidate_subst_constantCoeff _ _ (by simp),candidateLogZInU_constantCoeff,mul_zero]
  simpa only [neg_mul] using candidateExp_neg hz

end Dowling
