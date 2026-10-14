import Dowling.DowlingInverseZCandidateFactors

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- The ordinary binomial-product row, before the even-index correction. -/
def dowlingBinomialRow (a : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n+1), Polynomial.C (dowlingBinomialWeight a k*
    dowlingBinomialWeight a (n-k))*Polynomial.X^k

theorem dowlingBinomialSeries_scaled_coeff (a : ℝ) (n : ℕ) :
    coeff n ((dowlingBinomialSeries a).subst (C Polynomial.X*X))=
      Polynomial.C (dowlingBinomialWeight a n)*Polynomial.X^n := by
  rw [← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,dowlingBinomialSeries_coeff]
  ring

theorem dowlingBinomialProduct_coeff (a : ℝ) (n : ℕ) :
    coeff n (dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X))=
      dowlingBinomialRow a n := by
  rw [mul_comm,coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dowlingBinomialSeries_scaled_coeff,dowlingBinomialSeries_coeff]
  simp only [map_mul]
  ring

theorem dowlingBinomialRow_coeff (a : ℝ) (n k : ℕ) :
    (dowlingBinomialRow a n).coeff k=
      if k≤n then dowlingBinomialWeight a k*dowlingBinomialWeight a (n-k) else 0 := by
  simp only [dowlingBinomialRow,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- The signed quadratic correction has the exact source weights. -/
def dowlingQuadraticWeight (c : ℝ) (j : ℕ) : ℝ :=
  c^j/j.factorial - if j=0 then 0 else c^(j-1)/(j-1).factorial

def dowlingCorrectedQuadratic (c : ℝ) : PowerSeries (Polynomial ℝ) :=
  dowlingQuadraticExp c*(1-C Polynomial.X*X^2)

theorem dowlingCorrectedQuadratic_coeff_even (c : ℝ) (j : ℕ) :
    coeff (2*j) (dowlingCorrectedQuadratic c)=
      Polynomial.C (dowlingQuadraticWeight c j)*Polynomial.X^j := by
  rw [dowlingCorrectedQuadratic,mul_sub,mul_one,map_sub]
  cases j with
  | zero =>
    have hc : PowerSeries.constantCoeff (dowlingQuadraticExp c)=1 :=
      candidateExp_constantCoeff (by simp)
    simp [dowlingQuadraticWeight,hc]
  | succ j =>
    have he : dowlingQuadraticExp c*(C Polynomial.X*X^2)=
        C Polynomial.X*(dowlingQuadraticExp c*X^2) := by ring
    rw [he,coeff_C_mul,show 2*(j+1)=2*j+2 by omega,coeff_mul_X_pow,
      dowlingQuadraticExp_coeff_even]
    rw [show 2*j+2=2*(j+1) by omega,dowlingQuadraticExp_coeff_even]
    simp only [dowlingQuadraticWeight,Nat.add_one_ne_zero,ite_false,add_tsub_cancel_right,
      map_sub]
    ring

end Dowling
