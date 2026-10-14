import MainTheorems.WishartBlocks.SymmetricCoordinateContractions
import MainTheorems.WishartBlocks.RegularizedOperator
import MainTheorems.WishartBlocks.WishartCutoffIdentity
import MainTheorems.WishartBlocks.GaussianProductIntegral

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.Elementwise ContDiff

theorem rankTwoDirection_self {p : ℕ} (v : Fin p → ℝ) :
    rankTwoDirection v v = Matrix.vecMulVec v v := by
  unfold rankTwoDirection
  module

theorem rankTwoDirection_isHermitian {p : ℕ} (u v : Fin p → ℝ) :
    (rankTwoDirection u v).IsHermitian := by
  ext i j
  simp only [rankTwoDirection, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, star_trivial, smul_eq_mul]
  ring

theorem linear_wishart_coefficient_contraction {p : ℕ} (A : MatrixEuclidean p →L[ℝ] ℂ)
    (q s : ℝ) (u v : Fin p → ℝ) :
    (∑ ij : Fin p × Fin p, ((q - 1) * (u ij.1 * v ij.2 / s - v ij.1 * v ij.2) : ℂ) *
      A (matrixCoordinates p (symmetricDirection ij.1 ij.2))) =
      (q - 1 : ℂ) * (A (matrixCoordinates p (rankTwoDirection u v)) / (s : ℂ) -
        A (matrixCoordinates p (Matrix.vecMulVec v v))) := by
  rw [← rankTwoDirection_self v, linear_rankTwo_coordinates, linear_rankTwo_coordinates]
  simp only [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [div_eq_mul_inv]
  ring

theorem bilinear_wishart_coefficient_contraction {p : ℕ}
    (B : MatrixEuclidean p →L[ℝ] MatrixEuclidean p →L[ℝ] ℂ)
    {V : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosSemidef) (v : Fin p → ℝ) :
    (∑ ij : Fin p × Fin p, ∑ kl : Fin p × Fin p,
      (-2 * V ij.1 kl.1 * v ij.2 * v kl.2 : ℂ) *
        B (matrixCoordinates p (symmetricDirection ij.1 ij.2))
          (matrixCoordinates p (symmetricDirection kl.1 kl.2))) =
      -2 * ∑ a : Fin p, B (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt V i a) v))
        (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt V i a) v)) := by
  rw [bilinear_gram_coordinates, sqrt_column_gramSum hV, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  ring

theorem bilinear_gram_rankOne_add {p : ℕ}
    (B : MatrixEuclidean p →L[ℝ] MatrixEuclidean p →L[ℝ] ℂ)
    {V : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosSemidef) (u v : Fin p → ℝ) :
    (∑ a : Fin p, B
      (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt (V + Matrix.vecMulVec u u) i a) v))
      (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt (V + Matrix.vecMulVec u u) i a) v))) =
      (∑ a : Fin p, B (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt V i a) v))
        (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt V i a) v))) +
      B (matrixCoordinates p (rankTwoDirection u v)) (matrixCoordinates p (rankTwoDirection u v)) := by
  have hW : (V + Matrix.vecMulVec u u).PosSemidef := hV.add
    (by simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star u)
  have hU := bilinear_gram_coordinates B (fun _ : Fin 1 => u) v
  simp only [Fin.sum_univ_one, gramSum] at hU
  rw [bilinear_gram_coordinates, sqrt_column_gramSum hW,
    bilinear_gram_coordinates, sqrt_column_gramSum hV, hU]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Complex.ofReal_add,
    Complex.ofReal_mul, add_mul, Finset.sum_add_distrib]

noncomputable def matrixTestOperator {p : ℕ} (f : MatrixEuclidean p → ℂ)
    (q : ℝ) (v : EuclideanSpace ℝ (Fin p)) (W : Matrix (Fin p) (Fin p) ℝ) : ℂ :=
  (q : ℂ) * fderiv ℝ f (matrixCoordinates p W)
      (matrixCoordinates p (Matrix.vecMulVec (fun i => v i) (fun i => v i))) +
    2 * ∑ a : Fin p, fderiv ℝ (fderiv ℝ f) (matrixCoordinates p W)
      (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i)))
      (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i)))

theorem wishart_differential_contraction {p : ℕ} {f : MatrixEuclidean p → ℂ}
    (hf : ContDiff ℝ ∞ f) (q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) {s : ℝ} (hs : 0 < s)
    {x : OneRowInput p} (hx : x.1.PosSemidef) :
    (∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) f
        (matrixCoordinates p (oneRowWishartValue S (s • v) x))) =
      gaussianMatrixTestSecond f S v s x / 2 +
        (q - 1 : ℂ) * gaussianMatrixTestFirst f S v s x / (2 * (s : ℂ)) -
          matrixTestOperator f q v (oneRowWishartValue S (s • v) x) := by
  let W := oneRowWishartValue S (s • v) x
  let A := fderiv ℝ f (matrixCoordinates p W)
  let B := fderiv ℝ (fderiv ℝ f) (matrixCoordinates p W)
  let Y := fun i : Fin p => oneRowGaussianVector S v s x i
  have he : (∑ i : WishartDifferentialIndex p, (wishartDifferenceCoefficient q S v s i x : ℂ) *
      functionDirections ((wishartDifferenceDirections i).map (matrixCoordinates p)) f
        (matrixCoordinates p W)) =
      (∑ ij : Fin p × Fin p, ((q - 1) * (Y ij.1 * v ij.2 / s - v ij.1 * v ij.2) : ℂ) *
        A (matrixCoordinates p (symmetricDirection ij.1 ij.2))) +
      (∑ ij : Fin p × Fin p, ∑ kl : Fin p × Fin p,
        (-2 * x.1 ij.1 kl.1 * v ij.2 * v kl.2 : ℂ) *
          B (matrixCoordinates p (symmetricDirection ij.1 ij.2))
            (matrixCoordinates p (symmetricDirection kl.1 kl.2))) := by
    rw [Fintype.sum_sum_type]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro ij _
      change (((q - 1) * (Y ij.1 * v ij.2 / s - v ij.1 * v ij.2) : ℝ) : ℂ) *
        lineDeriv ℝ f (matrixCoordinates p W)
          (matrixCoordinates p (symmetricDirection ij.1 ij.2)) = _
      rw [((hf.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv]
      simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, A]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ij _
      apply Finset.sum_congr rfl
      intro kl _
      change ((-2 * x.1 ij.1 kl.1 * v ij.2 * v kl.2 : ℝ) : ℂ) *
        lineDeriv ℝ (fun y => lineDeriv ℝ f y
          (matrixCoordinates p (symmetricDirection kl.1 kl.2))) (matrixCoordinates p W)
          (matrixCoordinates p (symmetricDirection ij.1 ij.2)) = _
      rw [smooth_second_lineDeriv hf]
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, B]
  rw [he]
  have hc₁ := linear_wishart_coefficient_contraction A q s Y (fun i => v i)
  have hc₂ := bilinear_wishart_coefficient_contraction B hx (fun i => v i)
  rw [hc₁, hc₂, gaussianMatrixTestFirst_rankTwo, gaussianMatrixTestSecond_rankTwo]
  unfold matrixTestOperator
  have hW : W = x.1 + Matrix.vecMulVec Y Y := rfl
  have hGram := bilinear_gram_rankOne_add B hx Y (fun i => v i)
  rw [← hW] at hGram
  change _ = (4 * B (matrixCoordinates p (rankTwoDirection Y (fun i => v i)))
      (matrixCoordinates p (rankTwoDirection Y (fun i => v i))) +
    2 * A (matrixCoordinates p (Matrix.vecMulVec (fun i => v i) (fun i => v i)))) / 2 +
    (q - 1 : ℂ) * (2 * A (matrixCoordinates p (rankTwoDirection Y (fun i => v i)))) /
      (2 * (s : ℂ)) - ((q : ℂ) * A (matrixCoordinates p (Matrix.vecMulVec (fun i => v i) (fun i => v i))) +
        2 * ∑ a : Fin p, B
          (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i)))
          (matrixCoordinates p (rankTwoDirection (fun i => CFC.sqrt W i a) (fun i => v i))))
  rw [hGram]
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
  ring

namespace BlockPartition

theorem smoothProductEuclidean_operator {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℝ) (v : EuclideanSpace ℝ (Fin p))
    {W : Matrix (Fin p) (Fin p) ℝ} (hW : W.PosSemidef) :
    matrixTestOperator (P.smoothProductEuclidean ν ε) q v W =
      (P.regularizedProductOperator ν ε q v W : ℂ) := by
  have hf := P.smoothProductEuclidean_contDiff ν hε
  have hg : P.regularizedFloorGap ε (coordinatesMatrix p (matrixCoordinates p W)) := by
    simpa only [coordinatesMatrix_matrixCoordinates] using P.regularizedFloorGap_positive hW hε
  have hdir (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian) :
      fderiv ℝ (P.smoothProductEuclidean ν ε) (matrixCoordinates p W) (matrixCoordinates p H) =
        (P.regularizedProductDirectional ε ν H W : ℂ) := by
    rw [← ((hf.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv,
      P.smoothProductEuclidean_lineDeriv ν hε hg,
      coordinatesMatrix_matrixCoordinates, coordinatesMatrix_matrixCoordinates,
      symmetricMatrixPart_eq_of_hermitian hH, symmetricMatrixPart_eq_of_hermitian hW.1]
  have hhess (H J : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian) (hJ : J.IsHermitian) :
      fderiv ℝ (fderiv ℝ (P.smoothProductEuclidean ν ε)) (matrixCoordinates p W)
        (matrixCoordinates p J) (matrixCoordinates p H) =
        (P.regularizedProductHessian ε ν H J W : ℂ) := by
    rw [← smooth_second_lineDeriv hf, P.smoothProductEuclidean_second_lineDeriv ν hε hg,
      coordinatesMatrix_matrixCoordinates, coordinatesMatrix_matrixCoordinates,
      coordinatesMatrix_matrixCoordinates, symmetricMatrixPart_eq_of_hermitian hH,
      symmetricMatrixPart_eq_of_hermitian hJ, symmetricMatrixPart_eq_of_hermitian hW.1]
  unfold matrixTestOperator regularizedProductOperator
  rw [hdir _ (by
    simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star (fun i => v i)).1)]
  simp_rw [hhess _ _ (rankTwoDirection_isHermitian _ _) (rankTwoDirection_isHermitian _ _)]
  push_cast
  rfl

end BlockPartition
end ResearchMain.WishartBlocks
