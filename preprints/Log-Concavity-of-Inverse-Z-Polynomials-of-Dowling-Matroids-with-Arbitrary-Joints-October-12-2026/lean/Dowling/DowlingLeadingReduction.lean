import Dowling.DowlingLeadingLambert

noncomputable section
namespace Dowling
open PowerSeries

def dowlingLeadingLog (m : ℝ) : PowerSeries (Polynomial ℝ) :=
  C (Polynomial.C m⁻¹)*(X-C Polynomial.X*C (Polynomial.C (1/3 : ℝ))*X^3)

 theorem candidateK_cubic_weight :
    CandidateWeight 4 (candidateK+C (Polynomial.C (1/3 : ℝ))*X^3) := by
  have h := candidateWeight_realSeries (w := 4)
    (candidateKReal+C (1/3 : ℝ)*X^3) (by
      intro n hn
      interval_cases n <;>
        norm_num [candidateKReal,candidateHReal,candidateUReal,pow_two,coeff_C_mul,
          coeff_X_pow,coeff_X,coeff_mul,Finset.Nat.antidiagonal_succ,
          Finset.Nat.antidiagonal_zero,coeff_exp])
  simpa only [map_add,map_mul,map_C,map_pow,map_X,candidateK] using h

 theorem dowlingLeadingLog_weight (m : ℝ) : CandidateWeight 1 (dowlingLeadingLog m) := by
  have h : CandidateWeight 3 (C (Polynomial.C (1/3 : ℝ))*(X : PowerSeries (Polynomial ℝ))^3) := by
    simpa using (candidateWeight_X.pow 3).scalar_mul (1/3)
  have ht : CandidateWeight 1 (C Polynomial.X*C (Polynomial.C (1/3 : ℝ))*X^3) := by
    simpa only [mul_assoc] using h.parameter_mul
  exact (candidateWeight_X.sub ht).scalar_mul m⁻¹

 theorem dowlingPLogV_leading_difference (m : ℝ) :
    CandidateWeight 2 (dowlingPLogV m-dowlingLeadingLog m) := by
  have h := candidateK_cubic_weight.parameter_mul.scalar_mul m⁻¹
  convert h using 1
  dsimp [dowlingPLogV,dowlingLeadingLog]
  ring

 theorem dowlingPCandidate_leading_difference (m : ℝ) :
    CandidateWeight 2 (dowlingPCandidate m-1-
      (dowlingLeadingLog m).subst (dowlingLambertInverse.subst (C (Polynomial.C m)*X))) := by
  let v := dowlingVInverse.subst (C (Polynomial.C m)*X)
  let l := dowlingLambertInverse.subst (C (Polynomial.C m)*X)
  have hv : CandidateWeight 1 v := dowlingVInverse_weight.subst (candidateWeight_X.scalar_mul m)
  have hl : CandidateWeight 1 l := dowlingLambertInverse_weight.subst (candidateWeight_X.scalar_mul m)
  have hv0 := hv.constantCoeff_eq_zero (by omega)
  have hs := HasSubst.of_constantCoeff_zero' hv0
  have hbase : CandidateWeight 2 (candidateExp (dowlingPLogV m)-1-dowlingLeadingLog m) := by
    have h := (candidateWeight_exp_remainder (dowlingPLogV_weight m)).add
      (dowlingPLogV_leading_difference m)
    convert h using 1
    ring
  have hfirst := hbase.subst hv
  rw [← coe_substAlgHom hs,map_sub,map_sub,map_one,coe_substAlgHom] at hfirst
  have hdiff : CandidateWeight 2 (v-l) := by
    have h := dowlingVInverse_lambert_difference.subst (candidateWeight_X.scalar_mul m)
    have hm := HasSubst.of_constantCoeff_zero' (show
      (C (Polynomial.C m)*(X : PowerSeries (Polynomial ℝ))).constantCoeff=0 by simp)
    rw [← coe_substAlgHom hm,map_sub,coe_substAlgHom] at h
    exact h
  have hsecond := candidateWeight_subst_difference (dowlingLeadingLog_weight m) hv hl hdiff
  have h := hfirst.add hsecond
  change CandidateWeight 2 (dowlingPCandidate m-1-(dowlingLeadingLog m).subst l)
  convert h using 1
  dsimp [dowlingPCandidate,candidateExp,v]
  ring

/-- All odd-rank top coefficients reduce to the Lambert inverse expression. -/
theorem dowlingPCandidate_odd_top_reduction (m : ℝ) (k : ℕ) :
    (coeff (2*k+3) (dowlingPCandidate m)).coeff (k+1)=
      (coeff (2*k+3) ((dowlingLeadingLog m).subst
        (dowlingLambertInverse.subst (C (Polynomial.C m)*X)))).coeff (k+1) := by
  have h := dowlingPCandidate_leading_difference m (2*k+3) (k+1) (by omega)
  simpa only [map_sub,coeff_one,ite_eq_right (by omega : 2*k+3≠0),sub_zero,
    Polynomial.coeff_sub,sub_eq_zero] using h

end Dowling
