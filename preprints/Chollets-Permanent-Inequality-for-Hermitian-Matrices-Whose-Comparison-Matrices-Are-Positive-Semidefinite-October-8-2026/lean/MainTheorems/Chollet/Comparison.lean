import MainTheorems.Chollet.Positivity

open scoped ComplexOrder
open Matrix

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem comparison_hermitian {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (comparison A).IsHermitian := by
  ext i j
  change comparison A j i = comparison A i j
  by_cases h : i = j
  · subst j
    rfl
  · have hn : ‖A j i‖ = ‖A i j‖ := by rw [← hA.apply i j, norm_star]
    simp [comparison, h, Ne.symm h, hn]

omit [Fintype I] in
theorem comparison_term_bound (A : Matrix I I ℂ) (x : I → ℂ) (i j : I) :
    ‖x i‖ * comparison A i j * ‖x j‖ ≤ (star (x i) * A i j * x j).re := by
  by_cases h : i = j
  · subst j
    rw [show comparison A i i = (A i i).re by simp [comparison]]
    have he : star (x i) * A i i * x i = A i i * (x i * star (x i)) := by ring
    rw [he, Complex.star_def, Complex.mul_conj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.normSq_eq_norm_sq]
    nlinarith
  · have hb := (abs_le.mp (Complex.abs_re_le_norm (star (x i) * A i j * x j))).1
    simp only [norm_mul, norm_star] at hb
    simpa [comparison, h, mul_assoc] using hb

theorem ComparisonPSD.positiveSemidefinite {A : Matrix I I ℂ} (hA : ComparisonPSD A) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA.1
  intro x
  apply Complex.nonneg_iff.mpr
  constructor
  · have hm := hA.2.dotProduct_mulVec_nonneg (fun i => ‖x i‖)
    have hs : (star (fun i => ‖x i‖)) ⬝ᵥ ((comparison A) *ᵥ (fun i => ‖x i‖)) ≤
        (star x ⬝ᵥ (A *ᵥ x)).re := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
        Complex.re_sum]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using comparison_term_bound A x i j
    exact hm.trans hs
  · exact (hA.1.im_star_dotProduct_mulVec_self x).symm

theorem ComparisonPSD.permanent_nonneg {A : Matrix I I ℂ} (hA : ComparisonPSD A) :
    0 ≤ A.permanent.re := positiveSemidefinite_permanent_nonneg hA.positiveSemidefinite

end ResearchMain.Chollet
