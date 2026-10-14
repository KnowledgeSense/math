import Dowling.DowlingInverseZCandidateExpansion

noncomputable section
namespace Dowling
open PowerSeries Finset

/-- The original supported finite coefficient row, with no omitted diagonal terms. -/
def dowlingScalarCoefficient (a : ℝ) (n k : ℕ) : ℝ :=
  if k≤n then ∑ j ∈ range (min k (n-k)+1),
    dowlingQuadraticWeight (((n : ℝ)+a)/2) j*
      dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j) else 0

theorem dowlingBinomialRow_shifted_coeff (a w : ℝ) (n k j : ℕ) (hj : 2*j≤n) :
    (Polynomial.C w*Polynomial.X^j*dowlingBinomialRow a (n-2*j)).coeff k=
      if j≤k ∧ k+j≤n then
        w*dowlingBinomialWeight a (k-j)*dowlingBinomialWeight a (n-k-j) else 0 := by
  rw [mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul',dowlingBinomialRow_coeff]
  split_ifs with h1 h2 h3
  all_goals try omega
  · rw [show n-2*j-(k-j)=n-k-j by omega]
    ring
  all_goals simp_all

theorem dowlingInverseZKernel_coeff (a : ℝ) (n k : ℕ) :
    (coeff n (dowlingInverseZKernel a n)).coeff k=dowlingScalarCoefficient a n k := by
  rw [dowlingInverseZKernel_row,Polynomial.finsetSum_coeff]
  have hterm (j : ℕ) (hj : j∈range (n/2+1)) :=
    dowlingBinomialRow_shifted_coeff a (dowlingQuadraticWeight (((n : ℝ)+a)/2) j)
      n k j (by have := mem_range.mp hj; omega)
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k≤n
  · rw [dowlingScalarCoefficient,ite_eq_left hk]
    symm
    calc
      _ = ∑ j ∈ range (min k (n-k)+1),
          if j≤k ∧ k+j≤n then
            dowlingQuadraticWeight (((n : ℝ)+a)/2) j*
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
  · rw [dowlingScalarCoefficient,ite_eq_right hk]
    apply sum_eq_zero
    intro j hj
    rw [ite_eq_right (by omega)]

theorem dowlingInverseZCandidate_coeff_coeff (m : ℝ) (n k : ℕ) :
    (coeff n (dowlingInverseZCandidate m)).coeff k=m^n*dowlingScalarCoefficient m⁻¹ n k := by
  rw [dowlingInverseZCandidate_coeff_kernel,Polynomial.coeff_C_mul,dowlingInverseZKernel_coeff]

end Dowling
