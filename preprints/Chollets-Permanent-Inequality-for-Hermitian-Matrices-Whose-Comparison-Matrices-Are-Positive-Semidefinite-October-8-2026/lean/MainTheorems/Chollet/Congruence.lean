import MainTheorems.Chollet.PositiveScaling

noncomputable section

open Matrix
open scoped ComplexOrder

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def scaledMatrix (A : Matrix I I ℂ) (d : I → ℝ) : Matrix I I ℂ :=
  fun i j => (d i : ℂ) * A i j * (d j : ℂ)

omit [Fintype I] [DecidableEq I] in
theorem scaledMatrix_hermitian {A : Matrix I I ℂ} (hA : A.IsHermitian) (d : I → ℝ) :
    (scaledMatrix A d).IsHermitian := by
  apply IsHermitian.ext
  intro i j
  simp only [scaledMatrix, star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [show (starRingEnd ℂ) (A j i) = A i j from hA.apply i j]
  ring

omit [Fintype I] [DecidableEq I] in
theorem scaledMatrix_diagonal (A : Matrix I I ℂ) (d : I → ℝ) (i : I) :
    (scaledMatrix A d i i).re = d i ^ 2 * (A i i).re := by
  simp only [scaledMatrix, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  ring

omit [Fintype I] [DecidableEq I] in
theorem scaledMatrix_norm (A : Matrix I I ℂ) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (i j : I) :
    ‖scaledMatrix A d i j‖ = d i * ‖A i j‖ * d j := by
  simp only [scaledMatrix, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hd i), abs_of_nonneg (hd j)]

omit [Fintype I] in
theorem scaledMatrix_comparison (A : Matrix I I ℂ) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    comparison (scaledMatrix A d) = fun i j => d i * comparison A i j * d j := by
  funext i j
  by_cases he : i = j
  · subst j
    rw [show comparison (scaledMatrix A d) i i = (scaledMatrix A d i i).re by simp [comparison]]
    rw [show comparison A i i = (A i i).re by simp [comparison], scaledMatrix_diagonal]
    ring
  · simp only [comparison, ite_eq_right he, scaledMatrix_norm A d hd]
    ring

theorem scaledMatrix_row (A : Matrix I I ℂ) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (i : I) :
    d i * ((comparison A) *ᵥ d) i = (scaledMatrix A d i i).re -
      ∑ j ∈ Finset.univ.erase i, ‖scaledMatrix A d i j‖ := by
  change d i * (∑ j, comparison A i j * d j) = _
  rw [← Finset.add_sum_erase Finset.univ (fun j => comparison A i j * d j) (Finset.mem_univ i)]
  simp only [show comparison A i i = (A i i).re by simp [comparison]]
  rw [mul_add, Finset.mul_sum, scaledMatrix_diagonal]
  have he : ∑ j ∈ Finset.univ.erase i, d i * (comparison A i j * d j) =
      -∑ j ∈ Finset.univ.erase i, ‖scaledMatrix A d i j‖ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp only [comparison, ite_eq_right hij, scaledMatrix_norm A d hd]
    ring
  rw [he]
  ring

theorem comparison_positive_scaling (A : Matrix I I ℂ) (hM : (comparison A).PosDef) :
    ∃ d : I → ℝ, (∀ i, 0 < d i) ∧ ∀ i,
      (∑ j ∈ Finset.univ.erase i, ‖scaledMatrix A d i j‖) < (scaledMatrix A d i i).re := by
  obtain ⟨d, hd, he⟩ := positive_scaling_exists hM (by
    intro i j hij
    simp only [comparison, ite_eq_right hij]
    exact neg_nonpos.mpr (norm_nonneg _))
  refine ⟨d, hd, ?_⟩
  intro i
  have hr := scaledMatrix_row A d (fun j => (hd j).le) i
  rw [he] at hr
  simp only [Pi.one_apply, mul_one] at hr
  linarith [hd i]

theorem scaledMatrix_permanent (A : Matrix I I ℂ) (d : I → ℝ) :
    (scaledMatrix A d).permanent = ((∏ i, d i : ℝ) : ℂ) ^ 2 * A.permanent := by
  have h := permanent_diagonal_congruence A (fun i => (d i : ℂ))
  rw [← Complex.ofReal_prod] at h
  exact h

end ResearchMain.Chollet
