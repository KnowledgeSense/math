import Dowling.DowlingLeadingLagrange

noncomputable section
namespace Dowling
open PowerSeries

 theorem candidateExp_nat_mul {f : PowerSeries (Polynomial ℝ)} (hf : f.constantCoeff=0) (n : ℕ) :
    candidateExp f^n=candidateExp ((n : PowerSeries (Polynomial ℝ))*f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih]
    have he : ((n+1 : ℕ) : PowerSeries (Polynomial ℝ))*f=(n : PowerSeries (Polynomial ℝ))*f+f := by push_cast; ring
    rw [he,candidateExp_add (by simp [hf]) hf]

def dowlingQuadraticExp (c : ℝ) : PowerSeries (Polynomial ℝ) :=
  candidateExp (C (Polynomial.C c)*C Polynomial.X*X^2)

 theorem dowlingQuadraticExp_coeff_even (c : ℝ) (k : ℕ) :
    coeff (2*k) (dowlingQuadraticExp c)=Polynomial.C (c^k/k.factorial)*Polynomial.X^k := by
  have he : dowlingQuadraticExp c =
      (rescale (Polynomial.C c*Polynomial.X) (exp (Polynomial ℝ))).subst
        ((X : PowerSeries (Polynomial ℝ))^2) := by
    rw [rescale_eq_subst,smul_eq_C_mul,candidate_subst_rescale _ (by simp)]
    simp only [dowlingQuadraticExp,candidateExp,map_mul,mul_assoc]
  rw [he,coeff_subst_X_pow (by omega : 2≠0),ite_eq_left (dvd_mul_right 2 k),
    Nat.mul_div_right _ (by omega),Algebra.algebraMap_self,coeff_rescale,coeff_exp]
  have hc : algebraMap ℚ (Polynomial ℝ) (1/(k.factorial : ℚ))=
      Polynomial.C ((k.factorial : ℝ)⁻¹) := by simp [one_div]
  rw [hc]
  simp only [mul_pow,div_eq_mul_inv,map_mul,map_pow,RingHom.id_apply]
  ring

 theorem dowlingQuadraticExp_coeff_odd (c : ℝ) (k : ℕ) :
    coeff (2*k+1) (dowlingQuadraticExp c)=0 := by
  have he : dowlingQuadraticExp c =
      (rescale (Polynomial.C c*Polynomial.X) (exp (Polynomial ℝ))).subst
        ((X : PowerSeries (Polynomial ℝ))^2) := by
    rw [rescale_eq_subst,smul_eq_C_mul,candidate_subst_rescale _ (by simp)]
    simp only [dowlingQuadraticExp,candidateExp,map_mul,mul_assoc]
  rw [he,coeff_subst_X_pow (by omega : 2≠0),ite_eq_right (by omega : ¬2∣2*k+1)]

 theorem dowlingQuadraticExp_power (n : ℕ) :
    candidateExp (-dowlingQuadraticExponent)^n=dowlingQuadraticExp ((n : ℝ)/2) := by
  rw [candidateExp_nat_mul (by simp)]
  apply congrArg candidateExp
  simp only [dowlingQuadraticExponent,neg_mul,neg_neg,
    div_eq_mul_inv,one_mul,map_mul,map_natCast]
  ring

end Dowling
