import MainTheorems.WishartBlocks.GaussianMeanCurve
import MainTheorems.WishartBlocks.GramContractions

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise ContDiff

theorem rankTwoDirection_symmetric_sum {p : ℕ} (u v : Fin p → ℝ) :
    rankTwoDirection u v =
      ∑ ij : Fin p × Fin p, (u ij.1 * v ij.2) • symmetricDirection ij.1 ij.2 := by
  classical
  ext i j
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    symmetricDirection, rankTwoDirection, Matrix.add_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.single, ite_and]
  simp only [mul_add, Finset.sum_add_distrib]
  simp
  ring

theorem matrixCoordinates_rankTwo_sum {p : ℕ} (u v : Fin p → ℝ) :
    matrixCoordinates p (rankTwoDirection u v) =
      ∑ ij : Fin p × Fin p, (u ij.1 * v ij.2) • matrixCoordinates p (symmetricDirection ij.1 ij.2) := by
  rw [rankTwoDirection_symmetric_sum, map_sum]
  simp only [map_smul]

theorem linear_rankTwo_coordinates {p : ℕ} (A : MatrixEuclidean p →L[ℝ] ℂ)
    (u v : Fin p → ℝ) :
    A (matrixCoordinates p (rankTwoDirection u v)) =
      ∑ ij : Fin p × Fin p, (u ij.1 * v ij.2 : ℂ) *
        A (matrixCoordinates p (symmetricDirection ij.1 ij.2)) := by
  rw [matrixCoordinates_rankTwo_sum, map_sum]
  simp only [map_smul, Complex.real_smul, Complex.ofReal_mul]

theorem bilinear_rankTwo_coordinates {p : ℕ}
    (B : MatrixEuclidean p →L[ℝ] MatrixEuclidean p →L[ℝ] ℂ)
    (u v w z : Fin p → ℝ) :
    B (matrixCoordinates p (rankTwoDirection u v)) (matrixCoordinates p (rankTwoDirection w z)) =
      ∑ ij : Fin p × Fin p, ∑ kl : Fin p × Fin p,
        (u ij.1 * v ij.2 : ℂ) * (w kl.1 * z kl.2 : ℂ) *
          B (matrixCoordinates p (symmetricDirection ij.1 ij.2))
            (matrixCoordinates p (symmetricDirection kl.1 kl.2)) := by
  rw [matrixCoordinates_rankTwo_sum, map_sum]
  simp only [_root_.sum_apply, _root_.smul_apply,
    map_smul, Complex.real_smul, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro ij _
  rw [matrixCoordinates_rankTwo_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  simp only [map_smul, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem bilinear_gram_coordinates {p : ℕ} {κ : Type*} [Fintype κ]
    (B : MatrixEuclidean p →L[ℝ] MatrixEuclidean p →L[ℝ] ℂ)
    (U : κ → Fin p → ℝ) (v : Fin p → ℝ) :
    (∑ a, B (matrixCoordinates p (rankTwoDirection (U a) v))
      (matrixCoordinates p (rankTwoDirection (U a) v))) =
      ∑ ij : Fin p × Fin p, ∑ kl : Fin p × Fin p,
        (gramSum U ij.1 kl.1 * v ij.2 * v kl.2 : ℂ) *
          B (matrixCoordinates p (symmetricDirection ij.1 ij.2))
            (matrixCoordinates p (symmetricDirection kl.1 kl.2)) := by
  simp_rw [bilinear_rankTwo_coordinates]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro kl _
  simp only [gramSum, Matrix.sum_apply, Matrix.vecMulVec_apply, Complex.ofReal_mul,
    Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem smooth_second_lineDeriv {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (x u v : MatrixEuclidean p) :
    lineDeriv ℝ (fun y => lineDeriv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfd.differentiable (by simp)).differentiableAt
  have he : (fun y => lineDeriv ℝ f y v) = fun y => fderiv ℝ f y v := by
    funext y
    exact ((hf.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv
  rw [he, (hdf.clm_apply (differentiableAt_const v)).lineDeriv_eq_fderiv,
    fderiv_clm_apply hdf (differentiableAt_const v)]
  simp

theorem first_matrix_rankTwo {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    oneRowMatrixFirst S v s x = (2 : ℝ) •
      rankTwoDirection (fun i => oneRowGaussianVector S v s x i) (fun i => v i) := by
  unfold oneRowMatrixFirst rankTwoDirection
  module

theorem gaussianMatrixTestFirst_rankTwo {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    gaussianMatrixTestFirst f S v s x = 2 *
      fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
        (matrixCoordinates p (rankTwoDirection (fun i => oneRowGaussianVector S v s x i) (fun i => v i))) := by
  unfold gaussianMatrixTestFirst
  rw [first_matrix_rankTwo, map_smul, map_smul]
  simp

theorem gaussianMatrixTestSecond_rankTwo {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    gaussianMatrixTestSecond f S v s x = 4 *
      fderiv ℝ (fderiv ℝ f) (matrixCoordinates p (oneRowWishartValue S (s • v) x))
        (matrixCoordinates p (rankTwoDirection (fun i => oneRowGaussianVector S v s x i) (fun i => v i)))
        (matrixCoordinates p (rankTwoDirection (fun i => oneRowGaussianVector S v s x i) (fun i => v i))) +
      2 * fderiv ℝ f (matrixCoordinates p (oneRowWishartValue S (s • v) x))
        (matrixCoordinates p (Matrix.vecMulVec (fun i => v i) (fun i => v i))) := by
  unfold gaussianMatrixTestSecond
  rw [first_matrix_rankTwo]
  simp only [oneRowMatrixSecond, map_smul, _root_.smul_apply, Complex.real_smul]
  norm_num
  ring

end ResearchMain.WishartBlocks
