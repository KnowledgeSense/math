import Dowling.DowlingInverseZCandidateConvolution

noncomputable section
namespace Dowling
open PowerSeries

theorem dowlingBraidPrimitive_coeff_one : coeff 1 dowlingBraidPrimitive=1 := by
  simp only [dowlingBraidPrimitive,candidatePrimitive,coeff_mk,Nat.cast_one,inv_one,
    Polynomial.C_1,one_mul,Nat.sub_self,coeff_zero_eq_constantCoeff_apply,dowlingBraidZ]
  exact candidateExp_constantCoeff braidLogZCandidate_constantCoeff

theorem dowlingBlockCoordinate_coeff_one (m : ℝ) (hm : m≠0) :
    coeff 1 (dowlingBlockCoordinate m)=1 := by
  rw [dowlingBlockCoordinate,coeff_C_mul,← smul_eq_C_mul,← rescale_eq_subst,coeff_rescale,
    pow_one,dowlingBraidPrimitive_coeff_one,mul_one,← Polynomial.C_mul,inv_mul_cancel₀ hm,
    Polynomial.C_1]

/-- The flat convolution determines the unsigned inverse-Z series uniquely. -/
theorem dowlingInverseZCandidate_unique (m : ℝ) (hm : m≠0)
    (Y : PowerSeries (Polynomial ℝ))
    (hY : dowlingZCandidate m*Y.subst (-dowlingBlockCoordinate m)=1) :
    Y=dowlingInverseZCandidate m := by
  have hz : dowlingZCandidate m≠0 := by
    intro h
    have hc := congrArg PowerSeries.constantCoeff h
    simp at hc
  have h := mul_left_cancel₀ hz (hY.trans (dowlingInverseZCandidate_convolution m hm).symm)
  apply candidate_subst_injective (by simp) (q := -dowlingBlockCoordinate m) _ h
  rw [map_neg,dowlingBlockCoordinate_coeff_one m hm]
  exact isUnit_one.neg

end Dowling
