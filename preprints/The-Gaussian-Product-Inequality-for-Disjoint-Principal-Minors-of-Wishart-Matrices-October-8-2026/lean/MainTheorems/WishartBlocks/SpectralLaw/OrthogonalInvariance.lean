import MainTheorems.WishartBlocks.WishartCongruence
import Mathlib.LinearAlgebra.UnitaryGroup

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped MatrixOrder

theorem orthogonal_congruence_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) 1 = 1 := by
  change (U : Matrix (Fin n) (Fin n) ℝ) * 1 *
    (U : Matrix (Fin n) (Fin n) ℝ).transpose = 1
  simpa only [mul_one, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.mul_star_self_of_mem U.property

theorem bartlettLaw_isotropic_orthogonal_invariant {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ)).map
      (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ)) =
    bartlettLaw α (1 : Matrix (Fin n) (Fin n) ℝ) := by
  simpa only [orthogonal_congruence_one] using
    bartlettLaw_covariance_congruence hα hα Matrix.PosSemidef.one
      (U : Matrix (Fin n) (Fin n) ℝ)

theorem bartlettLaw_isotropic_integral_congruence {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ} (hG : Measurable G) :
    (∫ W, G (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W)
      ∂bartlettLaw α 1) = ∫ W, G W ∂bartlettLaw α 1 := by
  rw [← integral_map (measurable_matrixCongruence _).aemeasurable
    hG.aestronglyMeasurable, bartlettLaw_isotropic_orthogonal_invariant hα U]

theorem matrixCongruence_orthogonal_mul {n : ℕ}
    (U V : Matrix.orthogonalGroup (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    matrixCongruence (U * V : Matrix.orthogonalGroup (Fin n) ℝ) W =
      matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ)
        (matrixCongruence (V : Matrix (Fin n) (Fin n) ℝ) W) := by
  simp only [matrixCongruence, Matrix.UnitaryGroup.mul_val,
    Matrix.transpose_mul, Matrix.mul_assoc]

end ResearchMain.WishartBlocks
