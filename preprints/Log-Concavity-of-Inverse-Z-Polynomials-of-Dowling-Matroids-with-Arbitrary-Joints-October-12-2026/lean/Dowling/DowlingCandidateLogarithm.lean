import Dowling.DowlingCandidateExponential

noncomputable section
namespace Dowling
open PowerSeries

/-- The coefficientwise definition is the literal source logarithmic coordinate,
with the removable parameter division cleared. -/
theorem dowlingLogCoordinate_log_identity :
    C Polynomial.X * dowlingLogCoordinate =
      (log (Polynomial ℝ)).subst (C Polynomial.X * X) +
        C Polynomial.X * log (Polynomial ℝ) - C Polynomial.X * X := by
  apply PowerSeries.ext
  intro n
  rw [coeff_C_mul]
  simp only [map_sub,map_add,coeff_C_mul]
  rw [← smul_eq_C_mul, ← rescale_eq_subst, coeff_rescale]
  by_cases hn : n=0
  · subst n
    simp [dowlingLogCoordinate,coeff_log]
  · have hcast : algebraMap ℚ (Polynomial ℝ) ((-1 : ℚ)^(n+1)/n) =
        Polynomial.C ((-1 : ℝ)^(n+1)/n) := by simp
    simp only [dowlingLogCoordinate,coeff_mk,ite_eq_right hn,coeff_log,hcast,coeff_X]
    have hp : (Polynomial.X : Polynomial ℝ) * Polynomial.X^(n-1) = Polynomial.X^n := by
      rw [← pow_succ',Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    split_ifs with hn1
    · subst n
      norm_num
    · linear_combination Polynomial.C ((-1 : ℝ)^(n+1)/n) * hp

theorem candidate_scaled_log_derivative (t : Polynomial ℝ) :
    derivative ((log (Polynomial ℝ)).subst (C t*X)) * (1+C t*X) = C t := by
  have hs : HasSubst (C t*(X : PowerSeries (Polynomial ℝ))) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have h := congrArg (substAlgHom (R := Polynomial ℝ) hs)
    (derivative_log_mul_one_add_X (A := Polynomial ℝ))
  simp only [map_mul,map_add,map_one,substAlgHom_X,coe_substAlgHom] at h
  have hdt : derivative (C t*(X : PowerSeries (Polynomial ℝ))) = C t := by simp
  rw [derivative_subst hs,hdt]
  calc
    _ = C t * (((derivative (log (Polynomial ℝ))).subst (C t*X))*(1+C t*X)) := by ring
    _ = C t := by rw [h,mul_one]

theorem dowlingLogCoordinate_derivative :
    derivative dowlingLogCoordinate * (1+X) * (1+C Polynomial.X*X) =
      1-C Polynomial.X*X^2 := by
  have hd := congrArg (derivative (R := Polynomial ℝ)) dowlingLogCoordinate_log_identity
  simp only [map_sub,map_add,Derivation.leibniz,derivative_C,derivative_X,
    smul_eq_mul,mul_zero,mul_one,add_zero] at hd
  have ha := candidate_scaled_log_derivative Polynomial.X
  have hb := derivative_log_mul_one_add_X (A := Polynomial ℝ)
  have ht : (C Polynomial.X : PowerSeries (Polynomial ℝ)) ≠ 0 := by
    intro h
    have hc := congrArg PowerSeries.constantCoeff h
    simp at hc
  apply mul_left_cancel₀ ht
  linear_combination (1+X)*(1+C Polynomial.X*X)*hd + (1+X)*ha +
    C Polynomial.X*(1+C Polynomial.X*X)*hb

theorem braidLogZCandidate_derivative : derivative braidLogZCandidate =
    1+C Polynomial.X+C Polynomial.X*dowlingLogInverse := by
  simp [braidLogZCandidate,derivative_candidatePrimitive,Derivation.leibniz]

def candidateLogZInU : PowerSeries (Polynomial ℝ) :=
  log (Polynomial ℝ) + (log (Polynomial ℝ)).subst (C Polynomial.X*X) -
    C (Polynomial.C (1/2 : ℝ))*C Polynomial.X*X^2

 theorem braidLogZCandidate_subst_coordinate :
    braidLogZCandidate.subst dowlingLogCoordinate = candidateLogZInU := by
  apply derivative.ext
  · have hs : HasSubst dowlingLogCoordinate :=
      HasSubst.of_constantCoeff_zero' dowlingLogCoordinate_constantCoeff
    rw [derivative_subst hs,braidLogZCandidate_derivative]
    rw [← coe_substAlgHom hs,map_add,map_add,map_one,map_mul]
    simp only [coe_substAlgHom,subst_C,dowlingLogInverse_subst_coordinate]
    change (1+C Polynomial.X+C Polynomial.X*X)*derivative dowlingLogCoordinate = _
    have hden : (1+X)*(1+C Polynomial.X*X : PowerSeries (Polynomial ℝ)) ≠ 0 := by
      apply mul_ne_zero
      all_goals
        intro h
        have := congrArg PowerSeries.constantCoeff h
        simp at this
    apply mul_right_cancel₀ hden
    have hg := dowlingLogCoordinate_derivative
    have ha := candidate_scaled_log_derivative Polynomial.X
    have hb := derivative_log_mul_one_add_X (A := Polynomial ℝ)
    simp only [candidateLogZInU,map_sub,map_add,Derivation.leibniz,derivative_C,
      derivative_pow,derivative_X,smul_eq_mul,mul_zero,zero_add,mul_one]
    have hc : (2 : PowerSeries (Polynomial ℝ))*C (Polynomial.C (1/2 : ℝ))=1 := by
      have hreal : (2 : ℝ)*(1/2)=1 := by norm_num
      have h := congrArg (fun r : ℝ => (C (Polynomial.C r) : PowerSeries (Polynomial ℝ))) hreal
      simpa only [map_mul,map_ofNat,map_one] using h
    linear_combination (1+C Polynomial.X+C Polynomial.X*X)*hg -
      (1+X)*ha - (1+C Polynomial.X*X)*hb +
      C Polynomial.X*X*(1+X)*(1+C Polynomial.X*X)*hc
  · have hz : (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))).constantCoeff=0 := by simp
    have hl : PowerSeries.constantCoeff ((log (Polynomial ℝ)).subst (C Polynomial.X*(X : PowerSeries (Polynomial ℝ))))=0 := by
      rw [PowerSeries.constantCoeff_eq,constantCoeff_subst_of_constantCoeff_zero hz]
      exact constantCoeff_log
    rw [PowerSeries.constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero dowlingLogCoordinate_constantCoeff]
    simp [candidateLogZInU,hl]

end Dowling
