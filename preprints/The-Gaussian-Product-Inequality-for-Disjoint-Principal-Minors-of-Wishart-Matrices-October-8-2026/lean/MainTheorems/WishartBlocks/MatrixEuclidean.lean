import MainTheorems.WishartBlocks.MatrixLaplaceStrip
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

abbrev MatrixEuclidean (p : ℕ) := EuclideanSpace ℝ (Fin p × Fin p)

noncomputable def matrixCoordinates (p : ℕ) : Matrix (Fin p) (Fin p) ℝ →L[ℝ] MatrixEuclidean p :=
  (EuclideanSpace.equiv (Fin p × Fin p) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ij : Fin p × Fin p =>
      (ContinuousLinearMap.proj ij.2 : (Fin p → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj ij.1 : (Fin p → Fin p → ℝ) →L[ℝ] (Fin p → ℝ)))

noncomputable def coordinatesMatrix (p : ℕ) : MatrixEuclidean p →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => EuclideanSpace.proj (i, j)

@[simp] theorem matrixCoordinates_apply {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (i j : Fin p) : matrixCoordinates p A (i, j) = A i j := rfl

@[simp] theorem coordinatesMatrix_apply {p : ℕ} (x : MatrixEuclidean p) (i j : Fin p) :
    coordinatesMatrix p x i j = x (i, j) := rfl

@[simp] theorem coordinatesMatrix_matrixCoordinates {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    coordinatesMatrix p (matrixCoordinates p A) = A := by ext i j; rfl

@[simp] theorem matrixCoordinates_coordinatesMatrix {p : ℕ} (x : MatrixEuclidean p) :
    matrixCoordinates p (coordinatesMatrix p x) = x := by ext ij; cases ij; rfl

noncomputable def coordinateTrace (p : ℕ) : MatrixEuclidean p →L[ℝ] ℝ :=
  ∑ i : Fin p, EuclideanSpace.proj (i, i)

@[simp] theorem coordinateTrace_matrixCoordinates {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) : coordinateTrace p (matrixCoordinates p A) = A.trace := by
  simp [coordinateTrace, Matrix.trace]

noncomputable def symmetricMatrixPart {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := (1 / 2 : ℝ) • (A + A.transpose)

theorem symmetricMatrixPart_isHermitian {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    (symmetricMatrixPart A).IsHermitian := by
  ext i j
  simp only [symmetricMatrixPart, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, star_trivial, smul_eq_mul]
  ring

theorem trace_matrixCoordinates_inner {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.IsHermitian) :
    (A * W).trace = inner ℝ (matrixCoordinates p A) (matrixCoordinates p W) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, PiLp.inner_apply,
    Fintype.sum_prod_type, matrixCoordinates_apply, RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : W j i = W i j := by simpa only [star_trivial] using hW.apply i j
  rw [hij]
  ring

theorem trace_symmetricMatrixPart_mul {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.IsHermitian) :
    (symmetricMatrixPart A * W).trace = (A * W).trace := by
  have ht : (A.transpose * W).trace = (A * W).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hij : W i j = W j i := by simpa only [star_trivial] using hW.apply j i
    rw [hij]
  simp only [symmetricMatrixPart, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul, ht]
  ring

noncomputable def matrixFrequency {p : ℕ} (ξ : MatrixEuclidean p) :
    Matrix (Fin p) (Fin p) ℝ := (-2 * Real.pi) • symmetricMatrixPart (coordinatesMatrix p ξ)

theorem matrixFrequency_isHermitian {p : ℕ} (ξ : MatrixEuclidean p) :
    (matrixFrequency ξ).IsHermitian := by
  change (matrixFrequency ξ).conjTranspose = matrixFrequency ξ
  simp only [matrixFrequency, Matrix.conjTranspose_smul, star_trivial,
    (symmetricMatrixPart_isHermitian (coordinatesMatrix p ξ)).eq]

theorem matrixFrequency_trace {p : ℕ} (ξ : MatrixEuclidean p)
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.IsHermitian) :
    (matrixFrequency ξ * W).trace = -2 * Real.pi *
      inner ℝ ξ (matrixCoordinates p W) := by
  simp only [matrixFrequency, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    trace_symmetricMatrixPart_mul _ hW, trace_matrixCoordinates_inner _ hW,
    matrixCoordinates_coordinatesMatrix]

theorem matrix_trace_norm_bound {p : ℕ} (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖W.trace‖ ≤ (p : ℝ) * ‖W‖ := by
  calc
    ‖W.trace‖ ≤ ∑ i : Fin p, ‖W i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin p, ‖W‖ := Finset.sum_le_sum fun i _ =>
      Matrix.norm_entry_le_entrywise_sup_norm W
    _ = _ := by simp

end ResearchMain.WishartBlocks
