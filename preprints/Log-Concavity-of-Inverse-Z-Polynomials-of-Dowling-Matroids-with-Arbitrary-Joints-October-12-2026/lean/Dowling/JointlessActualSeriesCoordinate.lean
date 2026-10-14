import Dowling.JointlessActualSeries

noncomputable section
namespace Dowling
open PowerSeries

def jointlessComparison (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹)*dowlingLambertCoordinate

def jointlessBase (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  dowlingInverseZBase m⁻¹*(1-C (1+Polynomial.X)*jointlessComparison m+
    jointlessComparison m*C Polynomial.X*dowlingLeadingLog m)

@[simp] theorem jointlessComparison_constantCoeff (m : ℝ) :
    (jointlessComparison m).constantCoeff=0 := by simp [jointlessComparison]

theorem jointlessComparison_cancel (m : ℝ) (hm : m≠0) :
    C (Polynomial.C m)*jointlessComparison m=dowlingLambertCoordinate := by
  rw [jointlessComparison,← mul_assoc,candidate_scalar_inverse m hm,one_mul]

theorem jointless_scaled_inverse_subst (m : ℝ) (hm : m≠0) :
    PowerSeries.subst (jointlessComparison m)
      (dowlingLambertInverse.subst (C (Polynomial.C m)*X))=X := by
  rw [candidate_subst_rescale _ (jointlessComparison_constantCoeff m),jointlessComparison_cancel m hm,
    dowlingLambertInverse_subst_coordinate]

theorem jointlessSeries_subst_coordinate (m : ℝ) (hm : m≠0) :
    (jointlessSeries m).subst (jointlessComparison m)=jointlessBase m := by
  have hs := HasSubst.of_constantCoeff_zero' (jointlessComparison_constantCoeff m)
  have hv : HasSubst (dowlingLambertInverse.subst (C (Polynomial.C m)*X)) :=
    HasSubst.of_constantCoeff_zero' (by rw [candidate_subst_constantCoeff _ _ (by simp),dowlingLambertInverse_constantCoeff])
  have hy : (dowlingInverseZCandidate m).subst (jointlessComparison m)=dowlingInverseZBase m⁻¹ := by
    rw [dowlingInverseZCandidate,subst_comp_subst_apply hv hs,jointless_scaled_inverse_subst m hm,X_subst]
  have ht : (jointTauSeries m).subst (jointlessComparison m)=C Polynomial.X*dowlingLeadingLog m := by
    rw [jointTauSeries,candidate_subst_C_mul (jointlessComparison_constantCoeff m),
      subst_comp_subst_apply hv hs,jointless_scaled_inverse_subst m hm,X_subst]
  rw [jointlessSeries,← coe_substAlgHom hs,map_mul,map_add,map_sub,map_one,map_mul,
    map_mul,coe_substAlgHom,subst_C,subst_X hs,hy,ht]
  change dowlingInverseZBase m⁻¹*(1-C (1+Polynomial.X)*jointlessComparison m+
    jointlessComparison m*(C Polynomial.X*dowlingLeadingLog m))=jointlessBase m
  dsimp [jointlessBase]
  ring

/-- The ordinary formal residue change has the exact Lambert Jacobian and
retains the original fixed total degree. -/
theorem jointlessSeries_coeff_change (m : ℝ) (hm : m≠0) (n : ℕ) :
    coeff n (jointlessSeries m)=Polynomial.C (m^n)*coeff n
      (jointlessBase m*(candidateExp (-dowlingQuadraticExponent))^n*(1-C Polynomial.X*X^2)) := by
  let u := C (Polynomial.C m⁻¹)*candidateExp dowlingQuadraticExponent
  let v := C (Polynomial.C m)*candidateExp (-dowlingQuadraticExponent)
  have huv : u*v=1 := by
    dsimp [u,v]
    have hs := candidate_scalar_inverse m hm
    have he := candidateExp_neg dowlingQuadraticExponent_constantCoeff
    calc
      _ = (C (Polynomial.C m)*C (Polynomial.C m⁻¹))*
          (candidateExp dowlingQuadraticExponent*candidateExp (-dowlingQuadraticExponent)) := by ring
      _ = 1 := by rw [hs,he,mul_one]
  have hq : X*u=jointlessComparison m := by dsimp [u,jointlessComparison,dowlingLambertCoordinate]; ring
  have hd : derivative (jointlessComparison m)=C (Polynomial.C m⁻¹)*
      candidateExp dowlingQuadraticExponent*(1-C Polynomial.X*X^2) := by
    rw [jointlessComparison]
    simp only [Derivation.leibniz,derivative_C,mul_zero,add_zero,smul_eq_mul,
      dowlingLambertCoordinate_derivative,mul_assoc]
  rw [Fan.coeff_change_variable _ u v huv,hq,jointlessSeries_subst_coordinate m hm,hd]
  have he : jointlessBase m*(v^(n+1)*
      (C (Polynomial.C m⁻¹)*candidateExp dowlingQuadraticExponent*(1-C Polynomial.X*X^2)))=
      C (Polynomial.C (m^n))*(jointlessBase m*(candidateExp (-dowlingQuadraticExponent))^n*
        (1-C Polynomial.X*X^2)) := by
    dsimp [v]
    rw [mul_pow,pow_succ (candidateExp (-dowlingQuadraticExponent)),← map_pow,← map_pow,
      pow_succ m]
    have hc : C (Polynomial.C (m^n*m))*C (Polynomial.C m⁻¹)=C (Polynomial.C (m^n)) := by
      rw [← map_mul,← map_mul,mul_assoc,mul_inv_cancel₀ hm,mul_one]
    have hexp := candidateExp_neg dowlingQuadraticExponent_constantCoeff
    calc
      _ = (C (Polynomial.C (m^n*m))*C (Polynomial.C m⁻¹))*
          (candidateExp dowlingQuadraticExponent*candidateExp (-dowlingQuadraticExponent))*
          (jointlessBase m*(candidateExp (-dowlingQuadraticExponent))^n*(1-C Polynomial.X*X^2)) := by ring
      _ = _ := by rw [hc,hexp,mul_one]
  rw [he,coeff_C_mul]

end Dowling
