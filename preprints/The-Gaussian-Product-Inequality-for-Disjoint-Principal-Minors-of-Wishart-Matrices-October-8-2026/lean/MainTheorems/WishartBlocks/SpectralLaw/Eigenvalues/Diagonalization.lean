import MainTheorems.WishartBlocks.SpectralLaw.Eigenvalues.Continuity

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators

theorem ascendingSpectrum_diagonalization {n : ℕ} (W : SymmetricMatrix n) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      W.val = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (ascendingSpectrum W) *
        (U : Matrix (Fin n) (Fin n) ℝ).transpose := by
  let V := W.property.eigenvectorUnitary
  let e := spectralPermutation n
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => V i (e j)
  have hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
    calc
      A * A.transpose = (V : Matrix (Fin n) (Fin n) ℝ) *
          (V : Matrix (Fin n) (Fin n) ℝ).transpose := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.transpose_apply, A]
        exact Equiv.sum_comp e (fun k => V i k * V j k)
      _ = 1 := by
        simpa only [Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_eq_transpose_of_trivial] using
            Unitary.mul_star_self_of_mem V.property
  refine ⟨⟨A, hA⟩, ?_⟩
  calc
    W.val = (V : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal W.property.eigenvalues *
        (V : Matrix (Fin n) (Fin n) ℝ).transpose := by
      simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
        Function.id_comp] using W.property.spectral_theorem
    _ = A * Matrix.diagonal (ascendingSpectrum W) * A.transpose := by
      ext i j
      change (∑ k, ((V : Matrix (Fin n) (Fin n) ℝ) *
          Matrix.diagonal W.property.eigenvalues) i k * V j k) =
        ∑ k, (A * Matrix.diagonal (ascendingSpectrum W)) i k * A j k
      simp only [Matrix.mul_diagonal]
      change (∑ k, V i k * W.property.eigenvalues k * V j k) =
        ∑ k, V i (e k) * W.property.eigenvalues (e k) * V j (e k)
      exact (Equiv.sum_comp e (fun k => V i k * W.property.eigenvalues k * V j k)).symm

theorem sortedEigenvalues_diagonalization {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsHermitian) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      W = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (sortedEigenvalues n W) *
        (U : Matrix (Fin n) (Fin n) ℝ).transpose := by
  rw [sortedEigenvalues_eq_ascendingSpectrum hW]
  exact ascendingSpectrum_diagonalization ⟨W, hW⟩

end ResearchMain.WishartBlocks
