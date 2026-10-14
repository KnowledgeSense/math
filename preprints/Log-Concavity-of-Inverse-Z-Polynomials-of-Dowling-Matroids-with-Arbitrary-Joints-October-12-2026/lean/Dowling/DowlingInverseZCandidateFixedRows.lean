import Dowling.DowlingInverseZCandidateRaising

noncomputable section
namespace Dowling
open PowerSeries Finset

def dowlingWeightedCoefficient (c a : ℝ) (n k : ℕ) : ℝ :=
  if k≤n then ∑ j ∈ range (min k (n-k)+1),
    dowlingQuadraticWeight c j*dowlingBinomialWeight a (k-j)*
      dowlingBinomialWeight a (n-k-j) else 0

theorem dowlingFixedKernel_row (c a : ℝ) (n : ℕ) :
    coeff n (dowlingFixedKernel c a)=
      ∑ j ∈ range (n/2+1), Polynomial.C (dowlingQuadraticWeight c j)*Polynomial.X^j*
          dowlingBinomialRow a (n-2*j) := by
  have he : dowlingFixedKernel c a=dowlingCorrectedQuadratic c*
        (dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X)) := by
    dsimp [dowlingFixedKernel,dowlingFixedGaussianProduct,dowlingCorrectedQuadratic]
    ring
  rw [he,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [dowling_sum_even _ (by intro j; rw [dowlingCorrectedQuadratic_coeff_odd,zero_mul])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dowlingCorrectedQuadratic_coeff_even,dowlingBinomialProduct_coeff]

theorem dowlingFixedKernel_coeff (c a : ℝ) (n k : ℕ) :
    (coeff n (dowlingFixedKernel c a)).coeff k=dowlingWeightedCoefficient c a n k := by
  rw [dowlingFixedKernel_row,Polynomial.finsetSum_coeff]
  have hterm (j : ℕ) (hj : j∈range (n/2+1)) :=
    dowlingBinomialRow_shifted_coeff a (dowlingQuadraticWeight c j)
      n k j (by have := mem_range.mp hj; omega)
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k≤n
  · rw [dowlingWeightedCoefficient,ite_eq_left hk]
    symm
    calc
      _ = ∑ j ∈ range (min k (n-k)+1),
          if j≤k ∧ k+j≤n then dowlingQuadraticWeight c j*
              dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j) else 0 := by
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_left (by have := mem_range.mp hj; omega)]
      _ = _ := by
        apply sum_subset
        · intro j hj
          apply mem_range.mpr
          have := mem_range.mp hj
          omega
        · intro j hj hnot
          rw [ite_eq_right (by have := mem_range.mp hj; simp only [mem_range] at hnot; omega)]
  · rw [dowlingWeightedCoefficient,ite_eq_right hk]
    apply sum_eq_zero
    intro j hj
    rw [ite_eq_right (by omega)]

theorem dowlingFixedKernel_euler_coeff (a : ℝ) (n : ℕ) :
    Polynomial.C ((n : ℝ)+a)*coeff n (dowlingFixedKernel (((n : ℝ)+a)/2) a)=
      Polynomial.C a*coeff n (dowlingFixedKernel (((n : ℝ)+a)/2) (a+1)) := by
  have h := congrArg (coeff n) (dowlingFixedGaussianProduct_euler (((n : ℝ)+a)/2) a)
  rw [map_add,candidate_coeff_X_derivative,coeff_C_mul,map_add] at h
  have hc : 2*(((n : ℝ)+a)/2)=(n : ℝ)+a := by ring
  rw [hc,mul_assoc,mul_assoc,coeff_C_mul,coeff_C_mul] at h
  have he : dowlingFixedKernel (((n : ℝ)+a)/2) a=
      dowlingFixedGaussianProduct (((n : ℝ)+a)/2) a-
      C Polynomial.X*(X^2*dowlingFixedGaussianProduct (((n : ℝ)+a)/2) a) := by
    dsimp [dowlingFixedKernel]
    ring
  rw [he,map_sub,coeff_C_mul]
  rw [coeff_C_mul] at h
  simp only [map_add,map_natCast] at h ⊢
  linear_combination h

/-- Exponent raising keeps the actual Gaussian weight parameter fixed. -/
theorem dowlingScalarCoefficient_raised {a : ℝ} (ha : 0<a) (n k : ℕ) :
    dowlingScalarCoefficient a n k = a/((n : ℝ)+a)*
      dowlingWeightedCoefficient (((n : ℝ)+a)/2) (a+1) n k := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k) (dowlingFixedKernel_euler_coeff a n)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_C_mul,dowlingFixedKernel_coeff,
    dowlingFixedKernel_coeff] at h
  change ((n : ℝ)+a)*dowlingScalarCoefficient a n k = _ at h
  have hn : (n : ℝ)+a≠0 := by positivity
  apply (mul_left_cancel₀ hn)
  rw [h]
  field_simp

end Dowling
