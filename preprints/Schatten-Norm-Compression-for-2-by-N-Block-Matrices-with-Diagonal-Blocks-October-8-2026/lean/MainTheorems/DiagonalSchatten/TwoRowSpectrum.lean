import MainTheorems.DiagonalSchatten.HermitianTwoSpectrum

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

def rowMass (W : Matrix (Fin 2) J ℂ) (i : Fin 2) : ℝ := ∑ j, ‖W i j‖ ^ 2

def rowCross (W : Matrix (Fin 2) J ℂ) : ℂ := ∑ j, W 0 j * star (W 1 j)

omit [DecidableEq J] in
theorem rowMass_nonneg (W : Matrix (Fin 2) J ℂ) (i : Fin 2) : 0 ≤ rowMass W i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq J] in
theorem rowCross_norm_le (W : Matrix (Fin 2) J ℂ) :
    ‖rowCross W‖ ≤ ∑ j, ‖W 0 j‖ * ‖W 1 j‖ := by
  unfold rowCross
  simpa only [norm_mul, norm_star] using
    norm_sum_le Finset.univ (fun j => W 0 j * star (W 1 j))

omit [DecidableEq J] in
theorem rowCross_sq_le (W : Matrix (Fin 2) J ℂ) :
    ‖rowCross W‖ ^ 2 ≤ rowMass W 0 * rowMass W 1 := by
  have hbound := rowCross_norm_le W
  have hp : 0 ≤ ∑ j, ‖W 0 j‖ * ‖W 1 j‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorm := norm_nonneg (rowCross W)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
    (fun j => ‖W 0 j‖) (fun j => ‖W 1 j‖)
  unfold rowMass
  nlinarith

omit [DecidableEq J] in
theorem twoRow_gram (W : Matrix (Fin 2) J ℂ) :
    W * W.conjTranspose = hermitianTwo (rowMass W 0) (rowMass W 1) (rowCross W) := by
  ext i k
  fin_cases i <;> fin_cases k
  · change (∑ j, W 0 j * star (W 0 j)) = ((∑ j, ‖W 0 j‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa [← Complex.ofReal_pow] using Complex.mul_conj' (W 0 j)
  · rfl
  · change (∑ j, W 1 j * star (W 0 j)) = star (∑ j, W 0 j * star (W 1 j))
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul, star_star]
  · change (∑ j, W 1 j * star (W 1 j)) = ((∑ j, ‖W 1 j‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa [← Complex.ofReal_pow] using Complex.mul_conj' (W 1 j)

theorem schattenPower_twoRow {p : ℝ} (hp : 0 < p) (W : Matrix (Fin 2) J ℂ) :
    schattenPower p W =
      (twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W)) ^ (p / 2) +
        (twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W)) ^ (p / 2) := by
  rw [schattenPower_eq_row_gram_roots hp, twoRow_gram]
  exact rootPowerSum_hermitianTwo_of_nonneg p (rowCross W)
    (rowMass_nonneg W 0) (rowMass_nonneg W 1) (rowCross_sq_le W)

end

end ResearchMain.DiagonalSchatten
