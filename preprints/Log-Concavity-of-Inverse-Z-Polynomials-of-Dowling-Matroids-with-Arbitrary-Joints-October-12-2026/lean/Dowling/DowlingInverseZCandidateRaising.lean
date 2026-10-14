import Dowling.DowlingInverseZCandidatePositivity

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingBinomialSeries_add (a b : ℝ) :
    dowlingBinomialSeries (a+b)=dowlingBinomialSeries a*dowlingBinomialSeries b := by
  rw [dowlingBinomialSeries,dowlingBinomialSeries,dowlingBinomialSeries,
    ← candidateExp_add (dowlingBinomial_argument_constantCoeff a)
      (dowlingBinomial_argument_constantCoeff b)]
  congr 1
  simp only [map_add]
  ring

theorem dowlingBinomialSeries_one_inverse :
    dowlingBinomialSeries 1*(1-X)=1 := by
  have hz : PowerSeries.constantCoeff ((log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ)))=0 := by
    rw [candidate_subst_constantCoeff _ _ (by simp),constantCoeff_log]
  have he := candidateExp_log_subst (g := (-X : PowerSeries (Polynomial ℝ))) (by simp)
  change candidateExp (-C (Polynomial.C (1 : ℝ))*(log (Polynomial ℝ)).subst (-X : PowerSeries (Polynomial ℝ)))*(1-X)=1
  simp only [map_one,neg_one_mul]
  rw [show (1-X : PowerSeries (Polynomial ℝ))=1+(-X) by ring,← he,mul_comm]
  exact candidateExp_neg hz

theorem dowlingBinomialSeries_raise (a : ℝ) :
    dowlingBinomialSeries (a+1)*(1-X)=dowlingBinomialSeries a := by
  rw [dowlingBinomialSeries_add,mul_assoc,dowlingBinomialSeries_one_inverse,mul_one]

theorem dowlingBinomialSeries_derivative (a : ℝ) :
    derivative (dowlingBinomialSeries a)=C (Polynomial.C a)*dowlingBinomialSeries (a+1) := by
  have hne : (1-X : PowerSeries (Polynomial ℝ))≠0 := by
    intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp at h0
  apply mul_right_cancel₀ hne
  rw [dowlingBinomialSeries_differential,mul_assoc,dowlingBinomialSeries_raise]

/-- The Gaussian factor has a fixed exponent parameter while the binomial exponent rises. -/
def dowlingFixedGaussianProduct (c a : ℝ) : PowerSeries (Polynomial ℝ) :=
  dowlingQuadraticExp c*dowlingBinomialSeries a*
    (dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))

def dowlingFixedKernel (c a : ℝ) : PowerSeries (Polynomial ℝ) :=
  (1-C Polynomial.X*X^2)*dowlingFixedGaussianProduct c a

 theorem dowlingBinomialSeries_scaled_raise (a : ℝ) :
    (dowlingBinomialSeries (a+1)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))*(1-C Polynomial.X*X)=
      (dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) := by
  have hs : HasSubst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have h := congrArg (substAlgHom (R := Polynomial ℝ) hs) (dowlingBinomialSeries_raise a)
  simpa only [map_mul,map_sub,map_one,coe_substAlgHom,subst_X hs] using h

 theorem dowlingBinomialSeries_scaled_derivative (a : ℝ) :
    derivative ((dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))))=
      C Polynomial.X*C (Polynomial.C a)*(dowlingBinomialSeries (a+1)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' (by simp)),
    dowlingBinomialSeries_derivative,candidate_subst_C_mul (by simp)]
  have hd : derivative (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))=C Polynomial.X := by simp
  rw [hd]
  ring

 theorem dowlingQuadraticExp_derivative (c : ℝ) :
    derivative (dowlingQuadraticExp c)=
      dowlingQuadraticExp c*C (Polynomial.C (2*c))*C Polynomial.X*X := by
  have hd : derivative (C (Polynomial.C c)*C Polynomial.X*(X : PowerSeries (Polynomial ℝ))^2)=
      C (Polynomial.C (2*c))*C Polynomial.X*X := by
    simp only [Derivation.leibniz,derivative_C,derivative_pow,derivative_X,
      smul_eq_mul,mul_zero,zero_add,mul_one,map_mul,map_ofNat]
    ring
  rw [dowlingQuadraticExp,derivative_candidateExp (by simp),hd]
  ring

 theorem dowlingBinomialProduct_euler (a : ℝ) :
    dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) +
      X*dowlingBinomialSeries (a+1)*(dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) +
      C Polynomial.X*X*dowlingBinomialSeries a*(dowlingBinomialSeries (a+1)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))=
    (1-C Polynomial.X*X^2)*dowlingBinomialSeries (a+1)*
      (dowlingBinomialSeries (a+1)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) := by
  rw [← dowlingBinomialSeries_scaled_raise a,← dowlingBinomialSeries_raise a]
  ring

 theorem dowlingFixedGaussianProduct_euler (c a : ℝ) :
    X*derivative (dowlingFixedGaussianProduct c a)+C (Polynomial.C a)*dowlingFixedGaussianProduct c a=
      C (Polynomial.C (2*c))*C Polynomial.X*X^2*dowlingFixedGaussianProduct c a+
      C (Polynomial.C a)*dowlingFixedKernel c (a+1) := by
  have hd : derivative (dowlingFixedGaussianProduct c a)=
      derivative (dowlingQuadraticExp c)*dowlingBinomialSeries a*
        (dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) +
      dowlingQuadraticExp c*derivative (dowlingBinomialSeries a)*
        (dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))) +
      dowlingQuadraticExp c*dowlingBinomialSeries a*
        derivative ((dowlingBinomialSeries a).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ)))) := by
    simp only [dowlingFixedGaussianProduct,Derivation.leibniz,smul_eq_mul]
    ring
  rw [hd,dowlingQuadraticExp_derivative,dowlingBinomialSeries_derivative,
    dowlingBinomialSeries_scaled_derivative]
  dsimp only [dowlingFixedGaussianProduct,dowlingFixedKernel]
  linear_combination C (Polynomial.C a)*dowlingQuadraticExp c*dowlingBinomialProduct_euler a

end Dowling
