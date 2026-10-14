import Dowling.DowlingInverseZCandidatePrimitive

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingLambertCoordinate_neg :
    dowlingLambertCoordinate.subst (-X) = -dowlingLambertCoordinate := by
  have hz : PowerSeries.constantCoeff (-X : PowerSeries (Polynomial ℝ))=0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' hz
  have hq : dowlingQuadraticExponent.subst (-X)=dowlingQuadraticExponent := by
    rw [dowlingQuadraticExponent,← coe_substAlgHom hs]
    simp only [map_mul,map_neg,map_pow,coe_substAlgHom,subst_C,subst_X hs]
    change -C Polynomial.X*C (Polynomial.C (1/2 : ℝ))*(-X)^2 = _
    ring
  rw [dowlingLambertCoordinate,← coe_substAlgHom hs,map_mul,coe_substAlgHom,
    subst_X hs,candidateExp_subst dowlingQuadraticExponent_constantCoeff hz,hq]
  ring

/-- The negative logarithmic comparison coordinate has nonzero linear term. -/
def dowlingInverseComparison (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹)*dowlingLogCoordinate.subst (-X)

@[simp] theorem dowlingInverseComparison_constantCoeff (m : ℝ) :
    (dowlingInverseComparison m).constantCoeff=0 := by
  rw [dowlingInverseComparison,map_mul,constantCoeff_C,
    candidate_subst_constantCoeff _ _ (by simp),dowlingLogCoordinate_constantCoeff,mul_zero]

theorem dowlingInverseComparison_cancel (m : ℝ) (hm : m≠0) :
    C (Polynomial.C m)*dowlingInverseComparison m=dowlingLogCoordinate.subst (-X) := by
  rw [dowlingInverseComparison,← mul_assoc,candidate_scalar_inverse m hm,one_mul]

theorem dowlingBlockCoordinate_subst_comparison (m : ℝ) (hm : m≠0) :
    (dowlingBlockCoordinate m).subst (dowlingInverseComparison m)=
      -C (Polynomial.C m⁻¹)*dowlingLambertCoordinate := by
  have hn : HasSubst (-X : PowerSeries (Polynomial ℝ)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  rw [dowlingBlockCoordinate,candidate_subst_C_mul (dowlingInverseComparison_constantCoeff m),
    candidate_subst_rescale _ (dowlingInverseComparison_constantCoeff m),
    dowlingInverseComparison_cancel m hm,
    ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' dowlingLogCoordinate_constantCoeff) hn,
    dowlingBraidPrimitive_subst_coordinate,dowlingLambertCoordinate_neg]
  ring

theorem dowlingInverseComparison_linear_unit (m : ℝ) (hm : m≠0) :
    IsUnit (coeff 1 (dowlingInverseComparison m)) := by
  have he : dowlingLogCoordinate.subst (-X)=dowlingLogCoordinate.subst (C (-1 : Polynomial ℝ)*(X : PowerSeries (Polynomial ℝ))) := by simp
  rw [dowlingInverseComparison,coeff_C_mul,he,← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale]
  simp only [pow_one,dowlingLogCoordinate_coeff_one,mul_one]
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hm)).map Polynomial.C).mul (isUnit_one.neg)

end Dowling
