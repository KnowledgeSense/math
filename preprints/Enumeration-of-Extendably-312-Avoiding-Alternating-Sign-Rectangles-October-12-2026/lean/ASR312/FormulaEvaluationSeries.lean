import ASR312.FormulaEvaluationAlternating
import ASR312.FormulaEvaluationCatalanCoeff

noncomputable section
open PowerSeries Finset
open scoped BigOperators
namespace ASR312

/-- The generating series of all four terms of the specified integer formula. -/
def formulaSeries (r k : ℕ) : PowerSeries ℚ :=
  weightedBinomialSeries k*(B ((r:ℤ)-2)*(1-C 2*X^2))+B r+
    X*B ((r:ℤ)-1)*evenCatalanSeries.subst (X*(1+X))+
    C 2*(alternatingTail*B r)

theorem formulaSeries_coeff (r k d : ℕ) : coeff d (formulaSeries r k)=(F r k d:ℚ) := by
  unfold formulaSeries
  rw [map_add,map_add,map_add,weighted_binomial_product_coeff,coeff_B,
    catalan_product_coeff,coeff_C_mul,alternatingTail_binomial_coeff,Ring.choose_natCast]
  simp only [F,Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast,Int.cast_neg,Int.cast_one]

theorem B_two_step (r : ℤ) : B r=B (r-2)*(1+X)^2 := by
  have h := B_add (r-2) (2:ℤ)
  rw [show r-2+2=r by ring] at h
  have hb : B (2:ℤ)=(1+X:PowerSeries ℚ)^2 := B_nat 2
  rwa [hb] at h

theorem formulaSeries_closed (r k : ℕ) :
    formulaSeries r k =
      C (1/2)*B ((r:ℤ)-2)*((1-C 2*X^2)*(1+C 2*X)^k+1)+
      X*B ((r:ℤ)-1)*evenCatalanSeries.subst (X*(1+X)) := by
  have h1 : B (r:ℤ)=B ((r:ℤ)-2)*(1+X)^2 := B_two_step r
  have h2 : B ((r:ℤ)-1)=B ((r:ℤ)-2)*(1+X) := by
    have h := B_step ((r:ℤ)-2)
    rw [show (r:ℤ)-2+1=(r:ℤ)-1 by ring] at h
    exact h
  unfold formulaSeries weightedBinomialSeries
  rw [alternatingTail_mul_B,h1,h2]
  rw [show (C (2:ℚ):PowerSeries ℚ)=2 by exact map_ofNat C 2]
  linear_combination -B ((r:ℤ)-2)*(1-X^2)*C_half_mul_two

end ASR312
