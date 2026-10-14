import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped BigOperators
namespace AperyMoments

theorem alternating_binomial_polynomial (N r : ℕ) (hr : r ≤ N) :
    (∑ k ∈ Finset.range (r+1),
      C ((-1:ℝ)^k * r.choose k) * X^k * (1+X)^(N-k)) =
        (1+X : Polynomial ℝ)^(N-r) := by
  have hbin := add_pow (-X : Polynomial ℝ) (1+X) r
  have hsum : (∑ k ∈ Finset.range (r+1),
      C ((-1:ℝ)^k * r.choose k) * X^k * (1+X)^(N-k)) =
      (1+X)^(N-r) * (∑ k ∈ Finset.range (r+1),
        (-X)^k * (1+X)^(r-k) * (r.choose k : Polynomial ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : k ≤ r := by simpa using Finset.mem_range.mp hk
    have he : N-k = (N-r)+(r-k) := by omega
    rw [he,pow_add,neg_pow]
    simp only [map_mul,map_pow,map_neg,map_one,C_eq_natCast]
    ring
  rw [hsum, ← hbin]
  have he : (-X : Polynomial ℝ)+(1+X)=1 := by ring
  rw [he,one_pow,mul_one]

/-- An alternating binomial convolution valid throughout the original finite range. -/
theorem alternating_binomial_convolution (N r : ℕ) (hr : r ≤ N) :
    (∑ k ∈ Finset.range (r+1), (-1:ℝ)^k * r.choose k * (N-k).choose (r-k)) =
      ((N-r).choose r : ℝ) := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff r) (alternating_binomial_polynomial N r hr)
  rw [finsetSum_coeff,coeff_one_add_X_pow] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := by simpa using Finset.mem_range.mp hk
  simp only [mul_assoc,coeff_C_mul,coeff_X_pow_mul',ite_eq_left hkr,coeff_one_add_X_pow]

end AperyMoments
