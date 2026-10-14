import Dowling.DowlingMixtureFunctions

noncomputable section
namespace Dowling
open Finset

/-- The whole supported mixture is strictly log-concave at every internal index. -/
theorem dowlingWeightedCoefficient_strict_log_concave {c p : ℝ} (n k : ℕ)
    (hc : (n : ℝ)/2<c) (hp : 1<p) (hk : 1≤k) (hkn : k<n) :
    dowlingWeightedCoefficient c p n (k-1)*dowlingWeightedCoefficient c p n (k+1)<
      (dowlingWeightedCoefficient c p n k)^2 := by
  have h := discrete_midpoint_strict
    (dowlingMixtureFunction c p n (k-1)) (dowlingMixtureFunction c p n (k+1))
    (dowlingMixtureFunction c p n k) n
    (dowlingMixtureFunction_nonneg n (k-1) hc hp)
    (dowlingMixtureFunction_nonneg n (k+1) hc hp)
    (dowlingMixtureFunction_nonneg n k hc hp)
    (dowlingMixtureFunction_support c p n (k-1))
    (dowlingMixtureFunction_support c p n (k+1))
    (dowlingMixtureFunction_support c p n k)
    (dowlingMixtureFunction_midpoint_strict n k hc hp hk hkn)
    (mul_pos (dowlingMixtureFunction_sum_pos n (k-1) hc hp (by omega))
      (dowlingMixtureFunction_sum_pos n (k+1) hc hp (by omega)))
  simpa only [dowlingMixtureFunction_sum] using h

/-- Exact exponent raising transfers strictness to the original Dowling row. -/
theorem dowlingScalarCoefficient_strict_log_concave {a : ℝ} (ha : 0<a) (n k : ℕ)
    (hk : 1≤k) (hkn : k<n) :
    dowlingScalarCoefficient a n (k-1)*dowlingScalarCoefficient a n (k+1)<
      (dowlingScalarCoefficient a n k)^2 := by
  rw [dowlingScalarCoefficient_raised ha,dowlingScalarCoefficient_raised ha,
    dowlingScalarCoefficient_raised ha]
  have hc : (n : ℝ)/2<((n : ℝ)+a)/2 := by linarith
  have hp : 1<a+1 := by linarith
  have h := dowlingWeightedCoefficient_strict_log_concave n k hc hp hk hkn
  have hf : 0<a/((n : ℝ)+a) := div_pos ha (by positivity)
  have hs := mul_lt_mul_of_pos_left h (sq_pos_of_pos hf)
  nlinarith [hs]

end Dowling
