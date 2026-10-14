import Dowling.JointlessActualCoefficientsKernel

noncomputable section
namespace Dowling
open PowerSeries

def jointlessUnraisedKernel (a : ℝ) (n : ℕ) : PowerSeries (Polynomial ℝ) :=
  dowlingFixedKernel (((n : ℝ)+a)/2) a-
    C (Polynomial.C (a*n/(n+a-1)))*dowlingFixedKernel (((n : ℝ)+a-1)/2) a-
    C (Polynomial.C (a*(1-a)))*C Polynomial.X*X^2*dowlingFixedKernel (((n : ℝ)+a-1)/2) a-
    C (Polynomial.C (a^2/3))*C (Polynomial.X^2)*X^4*dowlingFixedKernel (((n : ℝ)+a-1)/2) a

theorem dowlingFixedKernel_lower_exponent (c a : ℝ) :
    dowlingFixedKernel c (a-1)=(1-X)*(1-C Polynomial.X*X)*dowlingFixedKernel c a := by
  have h1 := dowlingBinomialSeries_raise (a-1)
  have h2 := dowlingBinomialSeries_scaled_raise (a-1)
  rw [sub_add_cancel] at h1 h2
  dsimp [dowlingFixedKernel,dowlingFixedGaussianProduct]
  rw [← h2,← h1]
  ring

theorem jointlessRawKernel_expand (a : ℝ) (n : ℕ) :
    jointlessRawKernel a n=dowlingFixedKernel (((n : ℝ)+a)/2) a-
      C (Polynomial.C a)*dowlingFixedKernel (((n : ℝ)+a-1)/2) a+
      C (Polynomial.C a)*dowlingFixedKernel (((n : ℝ)+a-1)/2) (a-1)-
      C (Polynomial.C (a*(1-a)))*C Polynomial.X*X^2*dowlingFixedKernel (((n : ℝ)+a-1)/2) a-
      C (Polynomial.C (a^2/3))*C (Polynomial.X^2)*X^4*dowlingFixedKernel (((n : ℝ)+a-1)/2) a := by
  rw [dowlingFixedKernel_lower_exponent]
  simp only [jointlessRawKernel,map_mul,map_sub,map_one,map_add,map_pow]
  ring

theorem dowlingFixedKernel_lower_coeff (a : ℝ) (n : ℕ) (hn : (n : ℝ)+a-1≠0) :
    coeff n (dowlingFixedKernel (((n : ℝ)+a-1)/2) (a-1))=
      Polynomial.C ((a-1)/(n+a-1))*coeff n (dowlingFixedKernel (((n : ℝ)+a-1)/2) a) := by
  have h := dowlingFixedKernel_euler_coeff (a-1) n
  rw [sub_add_cancel,show (n : ℝ)+(a-1)=(n : ℝ)+a-1 by ring] at h
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hn)
  rw [h,← mul_assoc,← map_mul]
  congr 2
  field_simp

/-- Eliminate the linear coordinate term on the original homogeneous degree.
The exponent a−1 is allowed to be negative; only its scalar denominator is used. -/
theorem jointlessRawKernel_coeff_eq (a : ℝ) (n : ℕ) (hn : (n : ℝ)+a-1≠0) :
    coeff n (jointlessRawKernel a n)=coeff n (jointlessUnraisedKernel a n) := by
  rw [jointlessRawKernel_expand,jointlessUnraisedKernel]
  simp only [map_sub,map_add,coeff_C_mul]
  rw [dowlingFixedKernel_lower_coeff a n hn]
  have hs : a-a*((a-1)/(n+a-1))=a*n/(n+a-1) := by field_simp; ring
  have hp := congrArg (Polynomial.C : ℝ→+*Polynomial ℝ) hs
  simp only [map_sub,map_mul] at hp
  linear_combination -coeff n (dowlingFixedKernel (((n : ℝ)+a-1)/2) a)*hp

end Dowling
