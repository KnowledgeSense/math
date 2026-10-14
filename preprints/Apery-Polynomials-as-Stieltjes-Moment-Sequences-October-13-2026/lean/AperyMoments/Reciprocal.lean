import AperyMoments.Definitions

noncomputable section
open scoped BigOperators
namespace AperyMoments

theorem aperyPolynomial_zero (x : ℝ) : aperyPolynomial 0 x = 1 := by
  simp [aperyPolynomial]

theorem reciprocalPolynomial_zero (α : ℝ) : reciprocalPolynomial 0 α = 1 := by
  simp [reciprocalPolynomial]

/-- Exact reversal of the original Apéry sum, for every nonzero reciprocal parameter. -/
theorem reciprocalPolynomial_eq (n : ℕ) {α : ℝ} (hα : α ≠ 0) :
    reciprocalPolynomial n α = α ^ n * aperyPolynomial n α⁻¹ := by
  unfold reciprocalPolynomial aperyPolynomial
  rw [← Finset.sum_range_reflect
    (fun k => ((n.choose k : ℝ) * (2 * n - k).choose n) ^ 2 * α ^ k) (n + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using (Finset.mem_range.mp hj)
  have he : 2 * n - (n - j) = n + j := by omega
  simp only [Nat.add_sub_cancel, Nat.choose_symm hjn, he,
    Nat.choose_symm_of_eq_add (n := n + j) rfl, pow_sub₀ α hα hjn, inv_pow]
  ring

/-- All original coefficients are nonnegative; this alone is not a moment representation. -/
theorem aperyPolynomial_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ aperyPolynomial n x := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (pow_nonneg hx _)

end AperyMoments
