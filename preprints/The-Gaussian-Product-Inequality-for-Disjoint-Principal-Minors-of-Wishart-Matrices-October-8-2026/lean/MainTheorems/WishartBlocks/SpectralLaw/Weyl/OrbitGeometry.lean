import MainTheorems.WishartBlocks.SpectralLaw.Weyl.OrderedCoverage

namespace ResearchMain.WishartBlocks.Weyl

noncomputable def orthogonalDiagonal {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Q.val * Matrix.diagonal lam * Q.val.transpose

theorem orthogonalDiagonal_isHermitian {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    (orthogonalDiagonal Q lam).IsHermitian := by
  simpa only [orthogonalDiagonal, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose Q.val (Matrix.isHermitian_diagonal lam)

theorem orthogonalDiagonal_charpoly {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) :
    (orthogonalDiagonal Q lam).charpoly = (Matrix.diagonal lam).charpoly := by
  rw [orthogonalDiagonal, Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property,
    Matrix.one_mul]

theorem sortedEigenvalues_orthogonalDiagonal {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) {lam : Fin n → ℝ} (hlam : Monotone lam) :
    sortedEigenvalues n (orthogonalDiagonal Q lam) = lam := by
  rw [sortedEigenvalues_eq_ascendingSpectrum (orthogonalDiagonal_isHermitian Q lam)]
  exact (ascendingSpectrum_eq_iff ⟨_, orthogonalDiagonal_isHermitian Q lam⟩ lam).mpr
    ⟨hlam, orthogonalDiagonal_charpoly Q lam⟩

theorem orthogonalDiagonal_eq_iff_sign {n : ℕ}
    (Q V : Matrix.orthogonalGroup (Fin n) ℝ) {lam : Fin n → ℝ}
    (hlam : Function.Injective lam) :
    orthogonalDiagonal Q lam = orthogonalDiagonal V lam ↔
      ∃ s : Fin n → Bool, Q = V * signOrthogonal s := by
  constructor
  · intro heq
    let U : Matrix.orthogonalGroup (Fin n) ℝ := star V * Q
    have hU : U.val * Matrix.diagonal lam * U.val.transpose = Matrix.diagonal lam := by
      calc
        _ = V.val.transpose * orthogonalDiagonal Q lam * V.val := by
          simp only [U, Submonoid.coe_mul, Unitary.coe_star,
            Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.transpose_mul, Matrix.transpose_transpose, orthogonalDiagonal,
            Matrix.mul_assoc]
        _ = V.val.transpose * orthogonalDiagonal V lam * V.val := by rw [heq]
        _ = (V.val.transpose * V.val) * Matrix.diagonal lam *
            (V.val.transpose * V.val) := by simp only [orthogonalDiagonal, Matrix.mul_assoc]
        _ = Matrix.diagonal lam := by
          rw [(Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp V.property,
            Matrix.one_mul, Matrix.mul_one]
    obtain ⟨s, hs⟩ := orthogonal_stabilizer_is_sign U lam hlam hU
    refine ⟨s, ?_⟩
    calc
      Q = V * U := by simp only [U, ← mul_assoc, Unitary.mul_star_self, one_mul]
      _ = V * signOrthogonal s := by rw [hs]
  · rintro ⟨s, rfl⟩
    exact signedOrthogonal_congruence_diagonal V s lam

theorem orthogonalDiagonal_eq_transfer {n : ℕ}
    (Q V : Matrix.orthogonalGroup (Fin n) ℝ) {lam : Fin n → ℝ}
    (hlam : Function.Injective lam) (μ : Fin n → ℝ)
    (h : orthogonalDiagonal Q lam = orthogonalDiagonal V lam) :
    orthogonalDiagonal Q μ = orthogonalDiagonal V μ := by
  obtain ⟨s, hs⟩ := (orthogonalDiagonal_eq_iff_sign Q V hlam).mp h
  rw [hs]
  exact signedOrthogonal_congruence_diagonal V s μ

theorem ordered_orthogonalDiagonal_eq_iff {n : ℕ}
    (Q V : Matrix.orthogonalGroup (Fin n) ℝ) {lam μ : Fin n → ℝ}
    (hlam : StrictMono lam) (hμ : StrictMono μ) :
    orthogonalDiagonal Q lam = orthogonalDiagonal V μ ↔
      lam = μ ∧ ∃ s : Fin n → Bool, Q = V * signOrthogonal s := by
  constructor
  · intro h
    have heq : lam = μ := by
      have hs := congrArg (sortedEigenvalues n) h
      simpa only [sortedEigenvalues_orthogonalDiagonal Q hlam.monotone,
        sortedEigenvalues_orthogonalDiagonal V hμ.monotone] using hs
    refine ⟨heq, ?_⟩
    apply (orthogonalDiagonal_eq_iff_sign Q V hlam.injective).mp
    simpa only [← heq] using h
  · rintro ⟨rfl, hs⟩
    exact (orthogonalDiagonal_eq_iff_sign Q V hμ.injective).mpr hs

end ResearchMain.WishartBlocks.Weyl
