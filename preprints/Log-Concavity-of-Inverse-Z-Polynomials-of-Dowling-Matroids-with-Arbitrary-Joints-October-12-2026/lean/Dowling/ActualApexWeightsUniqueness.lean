import Dowling.ActualApexWeightsCoefficients

noncomputable section
namespace Dowling
open Finset

/-- The supported quadratic/binomial expansion is triangular with a strictly
positive diagonal, so its weights are determined by the polynomial row. -/
theorem quadraticWeightedRow_weights_unique {a : ℝ} (ha : 0<a) (v w : ℕ→ℝ) (n : ℕ)
    (he : ∀ k,quadraticWeightedRow v a n k=quadraticWeightedRow w a n k)
    (j : ℕ) (hj : 2*j≤n) : v j=w j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have h := he j
    rw [quadraticWeightedRow,quadraticWeightedRow,ite_eq_left (by omega),
      ite_eq_left (by omega),min_eq_left (by omega),sum_range_succ,sum_range_succ] at h
    have hs : ∑ i∈range j,v i*dowlingBinomialWeight a (j-i)*dowlingBinomialWeight a (n-j-i)=
        ∑ i∈range j,w i*dowlingBinomialWeight a (j-i)*dowlingBinomialWeight a (n-j-i) := by
      apply sum_congr rfl
      intro i hi
      rw [ih i (mem_range.mp hi) (by have := mem_range.mp hi; omega)]
    rw [hs] at h
    have hdiag : 0<dowlingBinomialWeight a (j-j)*dowlingBinomialWeight a (n-j-j) :=
      mul_pos (dowlingBinomialWeight_pos ha _) (dowlingBinomialWeight_pos ha _)
    nlinarith only [h,hdiag]

end Dowling
