import MainTheorems.WishartBlocks.WishartCongruence

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix

def matrixSelection {p m : ℕ} (e : Fin m → Fin p) : Matrix (Fin m) (Fin p) ℝ :=
  (1 : Matrix (Fin p) (Fin p) ℝ).submatrix e (Equiv.refl (Fin p))

theorem matrixSelection_congruence {p m : ℕ} (e : Fin m → Fin p)
    (W : Matrix (Fin p) (Fin p) ℝ) :
    matrixCongruence (matrixSelection e) W = W.submatrix e e := by
  unfold matrixCongruence matrixSelection
  rw [Matrix.one_submatrix_mul e (Equiv.refl _), Matrix.transpose_submatrix,
    Matrix.transpose_one, Matrix.mul_submatrix_one (Equiv.refl _) e]
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp,
    Matrix.submatrix_submatrix, Function.comp_id]

theorem bartlettLaw_principal_marginal {p m : ℕ} {α : ℝ}
    (hαp : (p : ℝ) - 1 < α) (hαm : (m : ℝ) - 1 < α)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) (e : Fin m → Fin p) :
    (bartlettLaw α S).map (fun W => W.submatrix e e) =
      bartlettLaw α (S.submatrix e e) := by
  have h := bartlettLaw_covariance_congruence hαp hαm hS (matrixSelection e)
  have he : matrixCongruence (matrixSelection e) =
      fun W : Matrix (Fin p) (Fin p) ℝ => W.submatrix e e :=
    funext (matrixSelection_congruence e)
  rw [he] at h
  exact h

theorem bartlettLaw_orthogonal_congruence {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {U : Matrix (Fin p) (Fin p) ℝ}
    (hU : U * U.transpose = 1) :
    (bartlettLaw α (1 : Matrix (Fin p) (Fin p) ℝ)).map (matrixCongruence U) =
      bartlettLaw α (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have h := bartlettLaw_covariance_congruence hα hα Matrix.PosSemidef.one U
  simpa only [matrixCongruence, Matrix.mul_one, hU] using h

end ResearchMain.WishartBlocks
