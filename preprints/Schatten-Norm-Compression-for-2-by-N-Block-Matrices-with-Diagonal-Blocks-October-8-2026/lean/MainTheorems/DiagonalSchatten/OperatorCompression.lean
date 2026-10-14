import MainTheorems.DiagonalSchatten.DiagonalBlocks
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

variable {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq I] [DecidableEq J] [DecidableEq D]

def groupVector (x : EuclideanSpace ℂ (I × D)) (i : I) : EuclideanSpace ℂ D :=
  WithLp.toLp 2 (fun d => x (i, d))

def groupNormVector (x : EuclideanSpace ℂ (I × D)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => (‖groupVector x i‖ : ℂ))

omit [DecidableEq I] [DecidableEq D] in
theorem groupNormVector_norm (x : EuclideanSpace ℂ (I × D)) :
    ‖groupNormVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, groupNormVector, groupVector, Fintype.sum_prod_type]

def operatorCompression (z : Fin 2 → J → D → ℂ) : Matrix (Fin 2) J ℂ :=
  fun i j => (‖diagonalBlock z i j‖ : ℂ)

omit [Fintype J] [DecidableEq J] in
theorem operatorCompression_nonnegative (z : Fin 2 → J → D → ℂ) (i : Fin 2) (j : J) :
    0 ≤ (operatorCompression z i j).re := norm_nonneg _

theorem groupVector_block_action (z : Fin 2 → J → D → ℂ)
    (x : EuclideanSpace ℂ (J × D)) (i : Fin 2) :
    groupVector ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
      (diagonalBlockMatrix z) x) i =
      ∑ j, Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (diagonalBlock z i j)
        (groupVector x j) := by
  apply (WithLp.ext_iff 2).mpr
  funext d
  change (∑ k : J × D, diagonalBlockMatrix z (i, d) k * x k) = _
  simp [Fintype.sum_prod_type, diagonalBlockMatrix, diagonalBlock,
    groupVector, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Matrix.diagonal_apply]

theorem groupVector_block_bound (z : Fin 2 → J → D → ℂ)
    (x : EuclideanSpace ℂ (J × D)) (i : Fin 2) :
    ‖groupVector ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (diagonalBlockMatrix z) x) i‖ ≤
      ∑ j, ‖diagonalBlock z i j‖ * ‖groupVector x j‖ := by
  rw [groupVector_block_action]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (diagonalBlock z i j)).le_opNorm
        (groupVector x j))

set_option maxHeartbeats 800000 in
theorem operatorCompression_action (z : Fin 2 → J → D → ℂ)
    (x : EuclideanSpace ℂ (J × D)) (i : Fin 2) :
    ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
      (operatorCompression z) (groupNormVector x)) i =
      ((∑ j, ‖diagonalBlock z i j‖ * ‖groupVector x j‖ : ℝ) : ℂ) := by
  change (∑ j, operatorCompression z i j * groupNormVector x j) = _
  simp [operatorCompression, groupNormVector, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

set_option maxHeartbeats 1500000 in
theorem diagonal_operator_compression (z : Fin 2 → J → D → ℂ) :
    ‖diagonalBlockMatrix z‖ ≤ ‖operatorCompression z‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let T := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (diagonalBlockMatrix z)
  let C := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (operatorCompression z)
  have houtput : ‖T x‖ ≤ ‖C (groupNormVector x)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← groupNormVector_norm (T x)]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have hb := groupVector_block_bound z x i
    have hn : 0 ≤ ∑ j, ‖diagonalBlock z i j‖ * ‖groupVector x j‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    change ‖(‖groupVector (T x) i‖ : ℂ)‖ ^ 2 ≤ ‖C (groupNormVector x) i‖ ^ 2
    rw [operatorCompression_action z x i, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    exact (sq_le_sq₀ (norm_nonneg _) hn).mpr hb
  exact houtput.trans (by
    simpa only [C, Matrix.l2_opNorm_def, groupNormVector_norm] using C.le_opNorm (groupNormVector x))

end

end ResearchMain.DiagonalSchatten
