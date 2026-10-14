import MainTheorems.WishartBlocks.SpectralLaw.Weyl.InverseCayley
import Mathlib.Analysis.Matrix.Spectrum

namespace ResearchMain.WishartBlocks.Weyl

noncomputable def spectralParameters {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) : LowerIndex n → ℝ :=
  fun e => if e.val.1 = e.val.2 then lam e.val.1 else z e

@[simp] theorem diagonalCoordinates_spectralParameters {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    diagonalCoordinates (spectralParameters lam z) = lam := by
  funext i
  change (if i = i then lam i else z ⟨toLex (i, i), le_refl i⟩) = lam i
  exact ite_eq_left rfl

@[simp] theorem skewMatrix_spectralParameters {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    skewMatrix (spectralParameters lam z) = skewMatrix z := by
  ext i j
  rcases lt_trichotomy j i with h | h | h
  · simp only [skewMatrix, dite_eq_left h]
    change (if i = j then lam i else z ⟨toLex (i, j), h.le⟩) = z ⟨toLex (i, j), h.le⟩
    exact ite_eq_right (ne_of_gt h)
  · subst j
    simp [skewMatrix]
  · simp only [skewMatrix, dite_eq_right (not_lt_of_gt h), dite_eq_left h]
    change -(if j = i then lam j else z ⟨toLex (j, i), h.le⟩) = -z ⟨toLex (j, i), h.le⟩
    rw [ite_eq_right (ne_of_gt h)]

noncomputable def globalSpectralMatrix {n : ℕ} (z : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (cayleyOrthogonalMatrix z).val * Matrix.diagonal (diagonalCoordinates z) *
    (cayleyOrthogonalMatrix z).val.transpose

noncomputable def globalSpectralCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    LowerIndex n → ℝ := symmetricCoordinates (globalSpectralMatrix z)

theorem globalSpectralMatrix_isHermitian {n : ℕ} (z : LowerIndex n → ℝ) :
    (globalSpectralMatrix z).IsHermitian := by
  simpa only [globalSpectralMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose (cayleyOrthogonalMatrix z).val
      (Matrix.isHermitian_diagonal (diagonalCoordinates z))

theorem signedOrthogonal_congruence_diagonal {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (s : Fin n → Bool) (lam : Fin n → ℝ) :
    (Q * signOrthogonal s).val * Matrix.diagonal lam *
      (Q * signOrthogonal s).val.transpose =
        Q.val * Matrix.diagonal lam * Q.val.transpose := by
  change (Q.val * signMatrix s) * Matrix.diagonal lam *
    (Q.val * signMatrix s).transpose = _
  rw [Matrix.transpose_mul]
  calc
    _ = Q.val * (signMatrix s * Matrix.diagonal lam * (signMatrix s).transpose) *
        Q.val.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [signMatrix_stabilizes_diagonal]

theorem isHermitian_exists_globalSpectralMatrix {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    ∃ z : LowerIndex n → ℝ,
      W = globalSpectralMatrix z ∧ diagonalCoordinates z = hW.eigenvalues := by
  let Q : Matrix.orthogonalGroup (Fin n) ℝ := hW.eigenvectorUnitary
  have hspectral : W = Q.val * Matrix.diagonal hW.eigenvalues * Q.val.transpose := by
    simpa only [Q, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hW.spectral_theorem
  obtain ⟨s, z, hz⟩ := orthogonal_has_signed_cayley_representation Q
  refine ⟨spectralParameters hW.eigenvalues z, ?_, diagonalCoordinates_spectralParameters _ _⟩
  have hQ : cayleyOrthogonalMatrix (spectralParameters hW.eigenvalues z) =
      Q * signOrthogonal s := by
    apply Subtype.ext
    change cayleyMatrix (skewMatrix (spectralParameters hW.eigenvalues z)) = _
    rw [skewMatrix_spectralParameters]
    exact congrArg Subtype.val hz
  rw [globalSpectralMatrix, hQ, diagonalCoordinates_spectralParameters,
    signedOrthogonal_congruence_diagonal]
  exact hspectral

theorem globalSpectralCoordinates_surjective (n : ℕ) :
    Function.Surjective (globalSpectralCoordinates (n := n)) := by
  intro x
  obtain ⟨z, hz, _⟩ := isHermitian_exists_globalSpectralMatrix (symmetricMatrix_isHermitian x)
  refine ⟨z, ?_⟩
  change symmetricCoordinates (globalSpectralMatrix z) = x
  rw [← hz, symmetricCoordinates_symmetricMatrix]

end ResearchMain.WishartBlocks.Weyl
