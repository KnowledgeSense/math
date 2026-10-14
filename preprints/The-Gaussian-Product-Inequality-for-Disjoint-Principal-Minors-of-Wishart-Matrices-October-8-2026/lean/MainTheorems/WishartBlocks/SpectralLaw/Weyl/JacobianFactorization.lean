import MainTheorems.WishartBlocks.SpectralLaw.Weyl.AngularDerivative
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.CongruenceVolume

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix.Norms.Operator

noncomputable def orthogonalCongruenceContinuousLinearMap {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (LowerIndex n → ℝ) →L[ℝ] (LowerIndex n → ℝ) :=
  (orthogonalCongruenceLinearMap Q).toContinuousLinearMap

theorem tangentMatrix_isHermitian {n : ℕ} (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    (tangentMatrix lam z).IsHermitian := by
  change (tangentMatrix lam z).conjTranspose = tangentMatrix lam z
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [tangentMatrix, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.diagonal_transpose, skewMatrix_transpose]
  noncomm_ring

set_option backward.isDefEq.respectTransparency false in
theorem jointExponentialCoordinates_hasFDerivAt {n : ℕ} (z : LowerIndex n → ℝ) :
    HasFDerivAt jointExponentialCoordinates
      ((orthogonalCongruenceContinuousLinearMap (exponentialOrthogonal z)).comp
        ((spectralDerivative (diagonalCoordinates z)).comp (angularDerivative z))) z := by
  have hQ := (exponentialOrthogonalMatrix_differentiable n z).hasFDerivAt
  have hQT := (transposeContinuousLinearMap n).hasFDerivAt.comp z hQ
  have hdiag := (diagonalContinuousLinearMap n).hasFDerivAt (x := z)
  have h := (lowerContinuousLinearMap n).hasFDerivAt.comp z ((hQ.mul' hdiag).mul' hQT)
  convert h using 1
  · rfl
  · ext w e
    change symmetricCoordinates (exponentialOrthogonalMatrix z *
      symmetricMatrix (spectralDerivative (diagonalCoordinates z) (angularDerivative z w)) *
        (exponentialOrthogonalMatrix z).transpose) e =
      symmetricCoordinates
        ((exponentialOrthogonalMatrix z * Matrix.diagonal (diagonalCoordinates z)) *
            (fderiv ℝ exponentialOrthogonalMatrix z w).transpose +
          (exponentialOrthogonalMatrix z * Matrix.diagonal (diagonalCoordinates w) +
          fderiv ℝ exponentialOrthogonalMatrix z w * Matrix.diagonal (diagonalCoordinates z)) *
            (exponentialOrthogonalMatrix z).transpose) e
    rw [← tangentMatrix_coordinates,
      symmetricMatrix_symmetricCoordinates (tangentMatrix_isHermitian _ _)]
    simp only [tangentMatrix, diagonalCoordinates_angularDerivative,
      skewMatrix_angularDerivative, exponentialOrthogonalMatrix_fderiv_factor,
      Matrix.transpose_mul, angularVelocity_transpose]
    congr 1
    noncomm_ring

theorem jointExponentialCoordinates_fderiv {n : ℕ} (z : LowerIndex n → ℝ) :
    fderiv ℝ jointExponentialCoordinates z =
      (orthogonalCongruenceContinuousLinearMap (exponentialOrthogonal z)).comp
        ((spectralDerivative (diagonalCoordinates z)).comp (angularDerivative z)) :=
  (jointExponentialCoordinates_hasFDerivAt z).fderiv

theorem jointExponentialCoordinates_abs_det {n : ℕ} (z : LowerIndex n → ℝ)
    (hz : StrictMono (diagonalCoordinates z)) :
    |(fderiv ℝ jointExponentialCoordinates z).det| =
      gapProduct (diagonalCoordinates z) * |(angularDerivative z).det| := by
  have hC : |LinearMap.det
      (orthogonalCongruenceLinearMap (exponentialOrthogonal z))| = 1 := by
    simpa only [LinearMap.det_toMatrix'] using
      orthogonalCongruence_abs_det (exponentialOrthogonal z)
  have hD : |LinearMap.det (spectralDerivative (diagonalCoordinates z)).toLinearMap| =
      gapProduct (diagonalCoordinates z) := by
    simpa only [LinearMap.det_toMatrix'] using spectralDerivative_abs_det hz
  rw [jointExponentialCoordinates_fderiv]
  change |LinearMap.det ((orthogonalCongruenceLinearMap (exponentialOrthogonal z)).comp
    ((spectralDerivative (diagonalCoordinates z)).toLinearMap.comp
      (angularDerivative z).toLinearMap))| = _
  rw [LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul, hC, one_mul, hD]

end ResearchMain.WishartBlocks.Weyl
