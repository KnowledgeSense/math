import MainTheorems.WishartBlocks.SpectralLaw.SpectralAverage
import MainTheorems.WishartBlocks.SpectralLaw.Eigenvalues.Diagonalization

namespace ResearchMain.WishartBlocks

theorem orthogonalAverage_eq_sortedSpectralAverage {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) :
    orthogonalAverage G W = orthogonalSpectralAverage G (sortedEigenvalues n W) := by
  have hd : positiveCoordinates (sortedEigenvalues n W) = sortedEigenvalues n W := by
    funext i
    exact max_eq_right (sortedEigenvalues_nonneg hW i)
  unfold orthogonalSpectralAverage
  rw [hd]
  obtain ⟨U, hU⟩ := sortedEigenvalues_diagonalization hW.1
  change W = matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ)
    (Matrix.diagonal (sortedEigenvalues n W)) at hU
  exact (congrArg (orthogonalAverage G) hU).trans
    (orthogonalAverage_congruence _ _ _)

end ResearchMain.WishartBlocks
