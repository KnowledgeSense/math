import MainTheorems.WishartBlocks.SpectralLaw.AveragingLaw
import MainTheorems.WishartBlocks.SpectralAveraging

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped MatrixOrder

noncomputable def orthogonalSpectralAverage {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ) (lam : Fin n → ℝ) : ℝ :=
  orthogonalAverage G (Matrix.diagonal (positiveCoordinates lam))

theorem orthogonalAverage_eq_spectralAverage {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef) :
    orthogonalAverage G W = orthogonalSpectralAverage G hW.1.eigenvalues := by
  have hd : positiveCoordinates hW.1.eigenvalues = hW.1.eigenvalues := by
    funext i
    exact max_eq_right (hW.eigenvalues_nonneg i)
  unfold orthogonalSpectralAverage
  rw [hd]
  have hs : W = matrixCongruence hW.1.eigenvectorUnitary
      (Matrix.diagonal hW.1.eigenvalues) := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp, matrixCongruence] using hW.1.spectral_theorem
  exact (congrArg (orthogonalAverage G) hs).trans
    (orthogonalAverage_congruence _ _ _)

theorem orthogonalSpectralAverage_nonneg {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hG : ∀ W, W.PosSemidef → 0 ≤ G W) (lam : Fin n → ℝ) :
    0 ≤ orthogonalSpectralAverage G lam := by
  apply integral_nonneg
  intro U
  exact hG _ (spectralMatrix_positiveSemidefinite
    (U : Matrix (Fin n) (Fin n) ℝ) lam)

end ResearchMain.WishartBlocks
