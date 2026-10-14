import MainTheorems.Chollet.Comparison

open scoped ComplexOrder

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem conjugate_positiveSemidefinite {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (conjugate A).PosSemidef := by
  have he : conjugate A = A.transpose := by ext i j; exact hA.isHermitian.apply j i
  rw [he]
  exact hA.transpose

omit [Fintype I] [DecidableEq I] in
theorem hadamard_positiveSemidefinite {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (hadamard A B).PosSemidef := hA.hadamard hB

theorem permanent_hadamard_conjugate (A : Matrix I I ℂ) :
    (hadamard A (conjugate A)).permanent.re = (squaredEntries A).permanent := by
  simp only [Matrix.permanent, hadamard, conjugate, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h : ∀ σ : Equiv.Perm I,
      (∏ i, ((‖A (σ i) i‖ ^ 2 : ℝ) : ℂ)).re = ∏ i, ‖A (σ i) i‖ ^ 2 := by
    intro σ
    rw [← Complex.ofReal_prod]
    rfl
  simp only [Complex.re_sum, h, squaredEntries]

theorem pair_bound_of_square_bounds {A B : Matrix I I ℂ}
    (hA : ComparisonPSD A) (hB : ComparisonPSD B)
    (hAA : (squaredEntries A).permanent ≤ A.permanent.re ^ 2)
    (hBB : (squaredEntries B).permanent ≤ B.permanent.re ^ 2) :
    (hadamard A B).permanent.re ≤ A.permanent.re * B.permanent.re := by
  have hPA := hA.permanent_nonneg
  have hPB := hB.permanent_nonneg
  have hPS := positiveSemidefinite_permanent_nonneg
    (hadamard_positiveSemidefinite hA.positiveSemidefinite hB.positiveSemidefinite)
  have hSA : 0 ≤ (squaredEntries A).permanent := by
    rw [permanent_squaredEntries]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSB : 0 ≤ (squaredEntries B).permanent := by
    rw [permanent_squaredEntries]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hCS := permanent_hadamard_cauchySchwarz A B
  have hmul := mul_le_mul hAA hBB hSB (sq_nonneg _)
  have hre := (sq_le_sq₀ hPS (norm_nonneg _)).mpr
    ((le_abs_self _).trans (Complex.abs_re_le_norm (hadamard A B).permanent))
  apply (sq_le_sq₀ hPS (mul_nonneg hPA hPB)).mp
  nlinarith

end ResearchMain.Chollet
