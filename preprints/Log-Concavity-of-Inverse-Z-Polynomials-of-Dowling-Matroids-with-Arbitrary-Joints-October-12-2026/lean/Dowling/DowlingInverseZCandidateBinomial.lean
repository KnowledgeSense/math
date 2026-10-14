import Dowling.DowlingInverseZCandidateUniqueness

noncomputable section
namespace Dowling
open PowerSeries

/-- Literal rising-factorial coefficient of the negative binomial series. -/
def dowlingBinomialWeight (a : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (a+j))/(n.factorial : ℝ)

def dowlingBinomialSeries (a : ℝ) : PowerSeries (Polynomial ℝ) :=
  candidateExp (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X))

theorem dowlingBinomial_argument_constantCoeff (a : ℝ) :
    PowerSeries.constantCoeff (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X))=0 := by
  rw [map_mul,candidate_subst_constantCoeff _ _ (by simp),constantCoeff_log,mul_zero]

@[simp] theorem dowlingBinomialSeries_constantCoeff (a : ℝ) :
    PowerSeries.constantCoeff (dowlingBinomialSeries a)=1 :=
  candidateExp_constantCoeff (dowlingBinomial_argument_constantCoeff a)

theorem dowlingBinomialWeight_zero (a : ℝ) : dowlingBinomialWeight a 0=1 := by
  simp [dowlingBinomialWeight]

theorem dowlingBinomialWeight_succ (a : ℝ) (n : ℕ) :
    (n+1 : ℝ)*dowlingBinomialWeight a (n+1)=(a+n)*dowlingBinomialWeight a n := by
  rw [dowlingBinomialWeight,dowlingBinomialWeight,Finset.prod_range_succ,Nat.factorial_succ]
  push_cast
  have hn : (n.factorial : ℝ)≠0 := by positivity
  have hn1 : (n+1 : ℝ)≠0 := by positivity
  field_simp

 theorem dowlingBinomialSeries_differential (a : ℝ) :
    derivative (dowlingBinomialSeries a)*(1-X)=C (Polynomial.C a)*dowlingBinomialSeries a := by
  have hl : derivative ((log (Polynomial ℝ)).subst (-X))*(1-X)=(-1 : PowerSeries (Polynomial ℝ)) := by
    simpa only [map_neg,map_one,neg_one_mul,sub_eq_add_neg] using candidate_scaled_log_derivative (-1)
  have hd : derivative (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X)) =
      -C (Polynomial.C a)*derivative ((log (Polynomial ℝ)).subst (-X)) := by
    simp [Derivation.leibniz]
  rw [dowlingBinomialSeries,derivative_candidateExp (dowlingBinomial_argument_constantCoeff a),hd]
  linear_combination -C (Polynomial.C a)*
    candidateExp (-C (Polynomial.C a)*(log (Polynomial ℝ)).subst (-X))*hl

 theorem dowlingBinomialSeries_coeff (a : ℝ) (n : ℕ) :
    coeff n (dowlingBinomialSeries a)=Polynomial.C (dowlingBinomialWeight a n) := by
  induction n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,dowlingBinomialWeight_zero]
  | succ n ih =>
    have h := congrArg (coeff n) (dowlingBinomialSeries_differential a)
    have hx : coeff n (derivative (dowlingBinomialSeries a)*X)=
        (n : Polynomial ℝ)*coeff n (dowlingBinomialSeries a) := by
      cases n with
      | zero => simp
      | succ n => rw [coeff_succ_mul_X,coeff_derivative]; push_cast; ring
    rw [mul_sub,mul_one,map_sub,hx,coeff_derivative,coeff_C_mul,ih] at h
    have hw := congrArg Polynomial.C (dowlingBinomialWeight_succ a n)
    simp only [map_mul,map_add,map_natCast,map_one] at hw
    have hn : (n+1 : Polynomial ℝ)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
    apply mul_left_cancel₀ hn
    linear_combination h-hw

 theorem dowlingBinomialWeight_pos {a : ℝ} (ha : 0<a) (n : ℕ) :
    0<dowlingBinomialWeight a n := by
  apply div_pos
  · exact Finset.prod_pos (fun j _ => by positivity)
  · positivity

end Dowling
