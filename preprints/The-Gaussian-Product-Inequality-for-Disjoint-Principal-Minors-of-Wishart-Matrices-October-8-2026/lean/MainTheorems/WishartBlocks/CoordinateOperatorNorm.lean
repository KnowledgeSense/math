import MainTheorems.WishartBlocks.MatrixEuclidean

namespace ResearchMain.WishartBlocks

open scoped Matrix.Norms.Elementwise

noncomputable def coordinatesOperatorNorm (p : ℕ) : ℝ :=
  ContinuousLinearMap.opNorm (F := Fin p → Fin p → ℝ) (coordinatesMatrix p)

theorem coordinatesOperatorNorm_nonneg (p : ℕ) : 0 ≤ coordinatesOperatorNorm p :=
  ContinuousLinearMap.opNorm_nonneg (F := Fin p → Fin p → ℝ) (coordinatesMatrix p)

theorem coordinatesMatrix_norm_bound {p : ℕ} (x : MatrixEuclidean p) :
    ‖coordinatesMatrix p x‖ ≤ coordinatesOperatorNorm p * ‖x‖ :=
  ContinuousLinearMap.le_opNorm (F := Fin p → Fin p → ℝ) (coordinatesMatrix p) x

end ResearchMain.WishartBlocks
