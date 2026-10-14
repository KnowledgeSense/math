import CircleKernel.PolynomialTailBound

noncomputable section
open Finset Polynomial
namespace CircleKernel

theorem exponentialTaylorPolynomial_tail (M : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B ≥ 0, ∀ t z : ℂ, ‖t‖ ≤ R → ‖z‖ ≤ 1 →
      ‖(exponentialTaylorPolynomial M t).eval z -
        ∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j‖ ≤ B*‖z‖^M := by
  let q := (exponentPolynomial M).map (Rat.castHom ℂ)
  choose B hBpos hB using fun ell : ℕ => polynomial_tail_bound (q^ell) M
  let C : ℕ → ℝ := fun ell => R^ell/(ell.factorial : ℝ)
  refine ⟨∑ ell ∈ range M, C ell*B ell, sum_nonneg (fun ell _ => mul_nonneg (by dsimp [C]; positivity) (hBpos ell)), ?_⟩
  intro t z ht hz
  have he : (exponentialTaylorPolynomial M t).eval z -
        (∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j) =
      ∑ ell ∈ range M, ((-t)^ell/(ell.factorial : ℂ)) *
        ((q^ell).eval z-∑ j ∈ range M, (q^ell).coeff j*z^j) := by
    have hc : (∑ j ∈ range M, (complexResiduePolynomial j).eval t*z^j) =
        ∑ ell ∈ range M, ((-t)^ell/(ell.factorial : ℂ)) *
          (∑ j ∈ range M, (q^ell).coeff j*z^j) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← exponentialTaylorPolynomial_coeff M j (mem_range.mp hj), exponentialTaylorPolynomial,
        finsetSum_coeff, sum_mul]
      simp only [coeff_C_mul, mul_assoc, q]
    rw [hc, exponentialTaylorPolynomial, eval_finsetSum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro ell hell
    simp only [eval_mul, eval_C, q]
    ring
  rw [he, sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ell hell
  rw [norm_mul]
  have hcoef : ‖(-t)^ell/(ell.factorial : ℂ)‖ ≤ C ell := by
    simp only [norm_div, norm_pow, norm_neg, Complex.norm_natCast, C]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht _) (by positivity)
  calc
    ‖(-t)^ell/(ell.factorial : ℂ)‖ *
        ‖(q^ell).eval z-∑ j ∈ range M, (q^ell).coeff j*z^j‖ ≤
      C ell*(B ell*‖z‖^M) := mul_le_mul hcoef (hB ell z hz) (norm_nonneg _) (by dsimp [C]; positivity)
    _ = _ := by ring

end CircleKernel
