import MainTheorems.WishartBlocks.SpectralLaw.Weyl.GlobalCoordinates
import MainTheorems.WishartBlocks.SpectralLaw.Eigenvalues.Diagonalization

namespace ResearchMain.WishartBlocks.Weyl

theorem congruence_exists_globalSpectralMatrix {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    ∃ z : LowerIndex n → ℝ,
      globalSpectralMatrix z = Q.val * Matrix.diagonal lam * Q.val.transpose ∧
        diagonalCoordinates z = lam := by
  obtain ⟨s, z, hz⟩ := orthogonal_has_signed_cayley_representation Q
  refine ⟨spectralParameters lam z, ?_, diagonalCoordinates_spectralParameters _ _⟩
  have hQ : cayleyOrthogonalMatrix (spectralParameters lam z) = Q * signOrthogonal s := by
    apply Subtype.ext
    change cayleyMatrix (skewMatrix (spectralParameters lam z)) = _
    rw [skewMatrix_spectralParameters]
    exact congrArg Subtype.val hz
  rw [globalSpectralMatrix, hQ, diagonalCoordinates_spectralParameters,
    signedOrthogonal_congruence_diagonal]

theorem isHermitian_exists_ordered_globalSpectralMatrix {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    ∃ z : LowerIndex n → ℝ,
      W = globalSpectralMatrix z ∧ diagonalCoordinates z = sortedEigenvalues n W := by
  obtain ⟨Q, hQ⟩ := sortedEigenvalues_diagonalization hW
  obtain ⟨z, hz, hlam⟩ := congruence_exists_globalSpectralMatrix Q (sortedEigenvalues n W)
  exact ⟨z, hQ.trans hz.symm, hlam⟩

theorem symmetricCoordinates_exists_ordered_globalSpectralCoordinates {n : ℕ}
    (W : LowerIndex n → ℝ) :
    ∃ z : LowerIndex n → ℝ,
      globalSpectralCoordinates z = W ∧
        diagonalCoordinates z = sortedEigenvalues n (symmetricMatrix W) := by
  obtain ⟨z, hz, hlam⟩ :=
    isHermitian_exists_ordered_globalSpectralMatrix (symmetricMatrix_isHermitian W)
  refine ⟨z, ?_, hlam⟩
  change symmetricCoordinates (globalSpectralMatrix z) = W
  rw [← hz, symmetricCoordinates_symmetricMatrix]

end ResearchMain.WishartBlocks.Weyl
