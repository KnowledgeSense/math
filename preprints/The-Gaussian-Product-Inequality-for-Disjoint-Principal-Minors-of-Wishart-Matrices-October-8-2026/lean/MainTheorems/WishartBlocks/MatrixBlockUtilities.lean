import MainTheorems.WishartBlocks.WishartRegressionDeterminant

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder

theorem trace_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix κ κ ℝ) :
    Matrix.trace (M.submatrix e e) = Matrix.trace M := by
  unfold Matrix.trace
  exact Fintype.sum_equiv e _ _ (fun i => rfl)

theorem trace_fromBlocks {k m : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin k) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin k) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp only [Matrix.trace, Fintype.sum_sum_type, Matrix.diag_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

theorem diagonal_blocks_positiveSemidefinite {k m : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {D : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.1.fromBlocks (by simp) hD.1)
  intro x
  have he : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [star_trivial, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [he]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

theorem regressionCovariance_positiveSemidefinite {k m : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hS : S.PosSemidef) (K : Matrix (Fin k) (Fin m) ℝ) :
    (regressionCovariance A S K).PosSemidef := by
  let C : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
    Matrix.fromBlocks 1 0 K.transpose 1
  have he : C * Matrix.fromBlocks A 0 0 S * C.transpose = regressionCovariance A S K := by
    simp only [C, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.transpose_transpose, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, zero_add, add_zero, Matrix.mul_one, Matrix.one_mul,
      regressionCovariance]
    congr 1
    exact add_comm _ _
  have h := (diagonal_blocks_positiveSemidefinite hA hS).mul_mul_conjTranspose_same C
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, he] using h

theorem precision_reindex_det {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (S T : Matrix κ κ ℝ) (c : ℝ) :
    (1 + c • (S.submatrix e e * T.submatrix e e)).det = (1 + c • (S * T)).det := by
  rw [Matrix.submatrix_mul_equiv]
  have he : 1 + c • (S * T).submatrix e e = (1 + c • (S * T)).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  rw [he, Matrix.det_submatrix_equiv_self]

def diagonalPairMatrix {k m : ℕ}
    (VW : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (k + m)) (Fin (k + m)) ℝ :=
  (Matrix.fromBlocks VW.1 0 0 VW.2).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def principalPair {k m : ℕ} (W : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ :=
  (W.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inl i)),
    W.submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun i => finSumFinEquiv (Sum.inr i)))

theorem principalPair_diagonalPairMatrix {k m : ℕ}
    (VW : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    principalPair (diagonalPairMatrix VW) = VW := by
  apply Prod.ext <;> ext i j <;>
    simp [principalPair, diagonalPairMatrix, Matrix.submatrix_apply]

theorem diagonalPairMatrix_injective {k m : ℕ} :
    Function.Injective (diagonalPairMatrix (k := k) (m := m)) := by
  intro VW XY h
  simpa only [principalPair_diagonalPairMatrix] using congrArg principalPair h

theorem measurable_diagonalPairMatrix {k m : ℕ} :
    Measurable (diagonalPairMatrix (k := k) (m := m)) := by
  apply Measurable.of_eval_matrix
  intro i j
  cases he : finSumFinEquiv.symm i <;> cases hf : finSumFinEquiv.symm j <;>
    simp [diagonalPairMatrix, Matrix.submatrix_apply, he, hf] <;> fun_prop

theorem measurable_principalPair {k m : ℕ} :
    Measurable (principalPair (k := k) (m := m)) := by
  unfold principalPair
  apply Measurable.prodMk <;> apply Measurable.of_eval_matrix <;>
    intro i j <;> fun_prop

theorem diagonalPairMatrix_positiveSemidefinite {k m : ℕ}
    {VW : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ}
    (hV : VW.1.PosSemidef) (hW : VW.2.PosSemidef) : (diagonalPairMatrix VW).PosSemidef :=
  (diagonal_blocks_positiveSemidefinite hV hW).submatrix finSumFinEquiv.symm

theorem principalPair_positiveSemidefinite {k m : ℕ}
    {W : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hW : W.PosSemidef) :
    (principalPair W).1.PosSemidef ∧ (principalPair W).2.PosSemidef :=
  ⟨hW.submatrix _, hW.submatrix _⟩

theorem trace_diagonalPairMatrix {k m : ℕ}
    (T : Matrix (Fin (k + m)) (Fin (k + m)) ℝ)
    (VW : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (T * diagonalPairMatrix VW) =
      Matrix.trace ((principalPair T).1 * VW.1) + Matrix.trace ((principalPair T).2 * VW.2) := by
  have he : T = (T.submatrix finSumFinEquiv finSumFinEquiv).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by ext i j; simp
  nth_rw 1 [he]
  rw [diagonalPairMatrix, Matrix.submatrix_mul_equiv, trace_reindex,
    ← Matrix.fromBlocks_toBlocks (T.submatrix finSumFinEquiv finSumFinEquiv),
    Matrix.fromBlocks_multiply, trace_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  rfl

theorem trace_diagonal_projection {k m : ℕ}
    (T W : Matrix (Fin (k + m)) (Fin (k + m)) ℝ) :
    Matrix.trace (T * diagonalPairMatrix (principalPair W)) =
      Matrix.trace (diagonalPairMatrix (principalPair T) * W) := by
  rw [trace_diagonalPairMatrix,
    Matrix.trace_mul_comm (diagonalPairMatrix (principalPair T)) W,
    trace_diagonalPairMatrix, Matrix.trace_mul_comm (principalPair W).1,
    Matrix.trace_mul_comm (principalPair W).2]

end ResearchMain.WishartBlocks
