import MainTheorems.WishartBlocks.WishartRegressionKernel

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder

def meanRowsMatrix {p r : ℕ} (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin r) (Fin p) ℝ := Matrix.of (fun i j => M i j)

noncomputable def rotateMeanRows {p r : ℕ} (O : Matrix (Fin r) (Fin r) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) : Fin r → EuclideanSpace ℝ (Fin p) :=
  fun i => WithLp.toLp 2 ((O * meanRowsMatrix M) i)

theorem meanRowsMatrix_gram {p r : ℕ} (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    meanRowGram M = (meanRowsMatrix M).transpose * meanRowsMatrix M := by
  ext i j
  simp only [meanRowGram, meanRowsMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

theorem rotateMeanRows_gram {p r : ℕ} {O : Matrix (Fin r) (Fin r) ℝ}
    (hO : O.transpose * O = 1) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    meanRowGram (rotateMeanRows O M) = meanRowGram M := by
  unfold rotateMeanRows
  rw [matrix_rows_gram, Matrix.transpose_mul, meanRowsMatrix_gram]
  calc
    _ = (meanRowsMatrix M).transpose * (O.transpose * O) * meanRowsMatrix M := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hO, Matrix.mul_one]

theorem noncentralWishart_rotate_mean_rows {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    {O : Matrix (Fin r) (Fin r) ℝ} (hO : O.transpose * O = 1)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    noncentralWishartLaw α S (rotateMeanRows O M) = noncentralWishartLaw α S M :=
  noncentralWishart_meanGram_eq hα hα hS _ _ (rotateMeanRows_gram hO M)

theorem meanRowGram_cons {p r : ℕ} (m : EuclideanSpace ℝ (Fin p))
    (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    meanRowGram (Fin.cons m M) = Matrix.vecMulVec (fun i => m i) (fun i => m i) + meanRowGram M := by
  rw [meanRowGram, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, meanRowGram]

end ResearchMain.WishartBlocks
