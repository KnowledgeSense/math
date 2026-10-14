import Dowling.DowlingCandidateComposition

noncomputable section
namespace Dowling
open PowerSeries

 theorem dowlingFlatCoordinate_subst_comparison (m : ℝ) (hm : m≠0) :
    (dowlingFlatCoordinate m).subst (dowlingComparisonCoordinate m)=
      C (Polynomial.C m⁻¹)*dowlingVCoordinate := by
  have hq := dowlingComparisonCoordinate_constantCoeff m
  have hs := HasSubst.of_constantCoeff_zero' hq
  have h := congrArg (substAlgHom (R := Polynomial ℝ) hs) (dowlingFlatCoordinate_cleared m)
  simp only [map_mul,map_sub,map_one,coe_substAlgHom,subst_C] at h
  have he : PowerSeries.subst (dowlingComparisonCoordinate m)
      (candidateExp (C (Polynomial.C m)*C Polynomial.X*X))=
        candidateExp (C Polynomial.X*candidateGofU) := by
    rw [candidateExp_subst (by simp) hq]
    rw [mul_assoc,candidate_subst_C_mul hq,candidate_subst_C_mul hq,
      subst_X hs]
    congr 1
    calc
      _ = C Polynomial.X*(C (Polynomial.C m)*dowlingComparisonCoordinate m) := by ring
      _ = _ := by rw [dowlingComparisonCoordinate_cancel m hm]
  rw [he,candidateGofU_exponential] at h
  change C (Polynomial.C m)*C Polynomial.X*
    ((dowlingFlatCoordinate m).subst (dowlingComparisonCoordinate m)) =
      1+C Polynomial.X*dowlingVCoordinate-1 at h
  have ht : (C (Polynomial.C m)*C Polynomial.X : PowerSeries (Polynomial ℝ))≠0 := by
    apply mul_ne_zero
    · intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      simp only [constantCoeff_C,map_zero] at hc
      have hv := congrArg (fun p : Polynomial ℝ => p.coeff 0) hc
      exact hm (by simpa using hv)
    · intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      simp at hc
  apply mul_left_cancel₀ ht
  rw [h]
  have hi := candidate_scalar_inverse m hm
  linear_combination -C Polynomial.X*dowlingVCoordinate*hi

 theorem dowlingZCandidate_subst_comparison (m : ℝ) (hm : m≠0) :
    (dowlingZCandidate m).subst (dowlingComparisonCoordinate m)=
      candidateExp (C (Polynomial.C m⁻¹)*(braidLogZCandidate.subst candidateGofU)) := by
  have hq := dowlingComparisonCoordinate_constantCoeff m
  have hb0 : PowerSeries.constantCoeff (braidLogZCandidate.subst (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))))=0 := by
    rw [candidate_subst_constantCoeff _ _ (by simp)]
    exact braidLogZCandidate_constantCoeff
  change PowerSeries.subst (dowlingComparisonCoordinate m)
    (candidateExp (C (Polynomial.C m⁻¹)*
      braidLogZCandidate.subst (C (Polynomial.C m)*X)))=_
  rw [candidateExp_subst (by simp [hb0]) hq,candidate_subst_C_mul hq,
    candidate_subst_rescale _ hq,dowlingComparisonCoordinate_cancel m hm]

 theorem dowlingPCandidate_subst_scaled_V (m : ℝ) (hm : m≠0) :
    (dowlingPCandidate m).subst (C (Polynomial.C m⁻¹)*dowlingVCoordinate)=
      candidateExp (dowlingPLogV m) := by
  have hs0 : (C (Polynomial.C m⁻¹)*dowlingVCoordinate).constantCoeff=0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' hs0
  have hi0 : PowerSeries.constantCoeff (dowlingVInverse.subst (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))))=0 := by
    rw [candidate_subst_constantCoeff _ _ (by simp)]
    exact dowlingVInverse_constantCoeff
  change PowerSeries.subst _ (PowerSeries.subst _ (candidateExp (dowlingPLogV m)))=_
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hi0) hs,
    candidate_subst_rescale _ hs0]
  have hc : C (Polynomial.C m)*(C (Polynomial.C m⁻¹)*dowlingVCoordinate)=dowlingVCoordinate := by
    rw [← mul_assoc,candidate_scalar_inverse m hm,one_mul]
  rw [hc,dowlingVInverse_subst_coordinate,X_subst]

/-- Exact formal flat-substitution equation for the explicitly constructed
strict-half-degree candidate and the original inverse-logarithm Z candidate. -/
theorem dowlingCandidate_flat_relation (m : ℝ) (hm : m≠0) :
    dowlingZCandidate m = candidateExp (C Polynomial.X*X) *
      (dowlingPCandidate m).subst (dowlingFlatCoordinate m) := by
  have hq := dowlingComparisonCoordinate_constantCoeff m
  have hs := HasSubst.of_constantCoeff_zero' hq
  apply candidate_subst_injective hq (dowlingComparisonCoordinate_linear_unit m hm)
  dsimp only
  rw [dowlingZCandidate_subst_comparison m hm]
  rw [← coe_substAlgHom hs,map_mul,coe_substAlgHom]
  rw [candidateExp_subst (by simp) hq,candidate_subst_C_mul_X hq]
  rw [subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' (dowlingFlatCoordinate_constantCoeff m)) hs,
    dowlingFlatCoordinate_subst_comparison m hm,dowlingPCandidate_subst_scaled_V m hm]
  have ha : C (Polynomial.C m⁻¹)*(braidLogZCandidate.subst candidateGofU)=
      C Polynomial.X*dowlingComparisonCoordinate m+dowlingPLogV m := by
    rw [braidLogZCandidate_subst_GofU,dowlingComparisonCoordinate,dowlingPLogV]
    ring
  rw [ha,candidateExp_add (by simp [hq]) (dowlingPLogV_constantCoeff m)]

end Dowling
