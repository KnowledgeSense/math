import MainTheorems.WishartBlocks.MatrixEuclidean

namespace ResearchMain.WishartBlocks

open scoped Matrix.Norms.Elementwise

noncomputable def matrixCoordinatesOperatorNorm (p : ℕ) : ℝ :=
  ContinuousLinearMap.opNorm (E := Fin p → Fin p → ℝ) (matrixCoordinates p)

theorem matrixCoordinatesOperatorNorm_nonneg (p : ℕ) :
    0 ≤ matrixCoordinatesOperatorNorm p :=
  ContinuousLinearMap.opNorm_nonneg (E := Fin p → Fin p → ℝ) (matrixCoordinates p)

theorem matrixCoordinates_norm_bound {p : ℕ} (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖matrixCoordinates p W‖ ≤ matrixCoordinatesOperatorNorm p * ‖W‖ :=
  ContinuousLinearMap.le_opNorm (E := Fin p → Fin p → ℝ) (matrixCoordinates p) W

end ResearchMain.WishartBlocks
