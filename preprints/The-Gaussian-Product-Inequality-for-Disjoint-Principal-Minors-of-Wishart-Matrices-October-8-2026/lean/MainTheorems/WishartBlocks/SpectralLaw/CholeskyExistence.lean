import MainTheorems.WishartBlocks.SpectralLaw.SymmetricCoordinates
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Algebra.Order.Star.Real

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem ldl_diagonal_positive {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : 0 < LDL.diagEntries hW i := by
  have hD : (LDL.diag hW).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hW.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hW))
  exact Matrix.posDef_diagonal_iff.mp hD i

theorem ldl_lower_diagonal_ne_zero {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : LDL.lower hW i i ≠ 0 := by
  have hd : (LDL.lower hW).det ≠ 0 := by
    rw [LDL.lower, Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using
      inv_ne_zero (Matrix.isUnit_det_of_invertible (LDL.lowerInv hW)).ne_zero
  rw [Matrix.det_of_isLowerTriangular _ (LDL.isLowerTriangular_lower hW)] at hd
  exact Finset.prod_ne_zero_iff.mp hd i (Finset.mem_univ _)

noncomputable def choleskyDiagonal {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : ℝ :=
  if 0 < LDL.lower hW i i then Real.sqrt (LDL.diagEntries hW i)
    else -Real.sqrt (LDL.diagEntries hW i)

noncomputable def choleskyFactor {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) : Matrix (Fin n) (Fin n) ℝ :=
  LDL.lower hW * Matrix.diagonal (choleskyDiagonal hW)

theorem choleskyDiagonal_sq {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) :
    choleskyDiagonal hW i * choleskyDiagonal hW i = LDL.diagEntries hW i := by
  unfold choleskyDiagonal
  split_ifs <;> nlinarith [Real.sq_sqrt (ldl_diagonal_positive hW i).le]

theorem choleskyFactor_lowerTriangular {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) : (choleskyFactor hW).IsLowerTriangular := by
  intro i j hij
  simp only [choleskyFactor, Matrix.mul_diagonal,
    LDL.isLowerTriangular_lower hW hij, zero_mul]

theorem choleskyFactor_diagonal_pos {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : 0 < choleskyFactor hW i i := by
  have hsqrt : 0 < Real.sqrt (LDL.diagEntries hW i) :=
    Real.sqrt_pos.mpr (ldl_diagonal_positive hW i)
  simp only [choleskyFactor, Matrix.mul_diagonal, choleskyDiagonal]
  split_ifs with h
  · exact mul_pos h hsqrt
  · have hneg : LDL.lower hW i i < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) (ldl_lower_diagonal_ne_zero hW i)
    exact mul_pos_of_neg_of_neg hneg (neg_neg_of_pos hsqrt)

theorem choleskyFactor_gram {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) : choleskyFactor hW * (choleskyFactor hW).transpose = W := by
  have hdiag : Matrix.diagonal (choleskyDiagonal hW) *
      Matrix.diagonal (choleskyDiagonal hW) = LDL.diag hW := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext (choleskyDiagonal_sq hW))
  calc
    _ = LDL.lower hW *
        (Matrix.diagonal (choleskyDiagonal hW) * Matrix.diagonal (choleskyDiagonal hW)) *
          (LDL.lower hW).transpose := by
      simp only [choleskyFactor, Matrix.transpose_mul, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
    _ = W := by
      rw [hdiag]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using LDL.lower_conj_diag hW

theorem lowerMatrix_symmetricCoordinates {n : ℕ}
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) :
    lowerMatrix (symmetricCoordinates L) = L := by
  ext i j
  unfold lowerMatrix lowerEntry
  split_ifs with h
  · rfl
  · simp only [zero_apply]
    exact (hL (lt_of_not_ge h)).symm

theorem choleskyCoordinates_surjective_positive {n : ℕ} (y : LowerIndex n → ℝ)
    (hy : (symmetricMatrix y).PosDef) :
    ∃ x : LowerIndex n → ℝ,
      (∀ i : Fin n, 0 < lowerMatrix x i i) ∧ choleskyCoordinates x = y := by
  let x := symmetricCoordinates (choleskyFactor hy)
  have hx : lowerMatrix x = choleskyFactor hy :=
    lowerMatrix_symmetricCoordinates (choleskyFactor_lowerTriangular hy)
  refine ⟨x, fun i => by rw [hx]; exact choleskyFactor_diagonal_pos hy i, ?_⟩
  change symmetricCoordinates (lowerMatrix x * (lowerMatrix x).transpose) = y
  rw [hx, choleskyFactor_gram, symmetricCoordinates_symmetricMatrix]

end ResearchMain.WishartBlocks
