import MainTheorems.WishartBlocks.SmoothProductDerivatives
import MainTheorems.WishartBlocks.LoewnerRankOne

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

theorem sqrt_column_gramSum {p : ℕ} {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    gramSum (fun a i => CFC.sqrt W i a) = W := by
  rw [gramSum_columns]
  have hs : (CFC.sqrt W).transpose = CFC.sqrt W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg W).posSemidef.1.eq
  rw [hs, CFC.sqrt_mul_sqrt_self W hW.nonneg]

namespace BlockPartition

noncomputable def regularizedProductOperator {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (ε q : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (W : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  q * P.regularizedProductDirectional ε ν (Matrix.vecMulVec (fun i => v i) (fun i => v i)) W +
    2 * ∑ a : Fin p, P.regularizedProductHessian ε ν
      (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i))
      (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i)) W

theorem regularizedProductOperator_nonneg {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {ε q : ℝ} (hε : 0 < ε)
    (hq : ∀ j, (P.size j : ℝ) + 1 ≤ q) (v : EuclideanSpace ℝ (Fin p))
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    0 ≤ P.regularizedProductOperator ν ε q v W := by
  classical
  let U := fun a : Fin p => fun i : (Σ j, Fin (P.size j)) => CFC.sqrt W (P.index i) a
  let u := fun i : (Σ j, Fin (P.size j)) => v (P.index i)
  have hGram : gramSum U = W.submatrix P.index P.index := by
    rw [← gramSum_submatrix (fun a i => CFC.sqrt W i a) P.index, sqrt_column_gramSum hW]
  have hWA (j : Fin d) : principalBlock (gramSum U) j ≤ P.regularizedBlocks ε W j := by
    rw [hGram]
    change P.block W j ≤ P.block W j + ε • 1
    change (P.block W j + ε • 1 - P.block W j).PosSemidef
    simpa only [add_sub_cancel_left] using
      (Matrix.PosSemidef.one : (1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ).PosSemidef).smul hε.le
  have h := determinant_product_operator_nonneg (P.regularizedBlocks ε W) ν q
    (P.regularizedBlocks_posDef hW hε) U u hWA hν hq
  convert h using 1
  congr 2

end BlockPartition
end ResearchMain.WishartBlocks
