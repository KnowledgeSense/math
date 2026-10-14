import MainTheorems.WishartBlocks.SpectralLaw.Weyl.WeightedPatchAveraging
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.AngleInvariance

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Operator

theorem coordinateOrthogonalAverageNN_jointExponentialCoordinates {n : ℕ}
    (G : (LowerIndex n → ℝ) → ℝ≥0∞) (z : LowerIndex n → ℝ) :
    coordinateOrthogonalAverageNN G (jointExponentialCoordinates z) =
      coordinateOrthogonalAverageNN G
        (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z))) := by
  have hcoord : jointExponentialCoordinates z =
      orthogonalCongruenceLinearMap (exponentialOrthogonal z)
        (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z))) := by
    change symmetricCoordinates (orthogonalDiagonal (exponentialOrthogonal z)
      (diagonalCoordinates z)) = symmetricCoordinates ((exponentialOrthogonal z).val *
        symmetricMatrix (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z))) *
          (exponentialOrthogonal z).val.transpose)
    rw [symmetricMatrix_symmetricCoordinates (Matrix.isHermitian_diagonal _)]
    rfl
  rw [hcoord, coordinateOrthogonalAverageNN_congruence]

theorem angularPatch_lintegral_changeOfVariables {n : ℕ} {lam₀ : Fin n → ℝ}
    (hlam₀ : StrictMono lam₀) {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ W, G W) =
      (orthogonalHaar n (angularOrbitPatch lam₀ hlam₀.injective lam₀))⁻¹ *
        ∫⁻ z in angularPatchDomain lam₀ hlam₀.injective,
          ENNReal.ofReal (gapProduct (diagonalCoordinates z) *
            |(angularDerivative (angleCoordinates z)).det|) *
              coordinateOrthogonalAverageNN G
                (symmetricCoordinates (Matrix.diagonal (diagonalCoordinates z))) := by
  let s := angularPatchDomain lam₀ hlam₀.injective
  let image := jointExponentialCoordinates '' s
  let mass := orthogonalHaar n (angularOrbitPatch lam₀ hlam₀.injective lam₀)
  have hs : MeasurableSet s := (angularPatchDomain_isOpen _ _).measurableSet
  have himage : MeasurableSet image := angularPatch_image_measurable _ _
  have havg : Measurable (coordinateOrthogonalAverageNN G) :=
    coordinateOrthogonalAverageNN_measurable hG
  calc
    _ = ∫⁻ W, angularPatchNNWeight lam₀ hlam₀.injective (symmetricMatrix W) *
        coordinateOrthogonalAverageNN G W := angularPatch_lintegral_average hlam₀ hG
    _ = ∫⁻ W, image.indicator (fun W => mass⁻¹ * coordinateOrthogonalAverageNN G W) W := by
      apply lintegral_congr
      intro W
      simp only [angularPatchNNWeight, symmetricCoordinates_symmetricMatrix]
      exact (image.indicator_mul_left (i := W) (fun _ => mass⁻¹)
        (coordinateOrthogonalAverageNN G)).symm
    _ = mass⁻¹ * ∫⁻ W in image, coordinateOrthogonalAverageNN G W := by
      rw [lintegral_indicator himage, lintegral_const_mul _ havg]
    _ = mass⁻¹ * ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ jointExponentialCoordinates z).det| *
        coordinateOrthogonalAverageNN G (jointExponentialCoordinates z) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (volume : Measure (LowerIndex n → ℝ)) hs
        (fun z _ => (jointExponentialCoordinates_differentiable n z).hasFDerivAt.hasFDerivWithinAt)
        (angularPatchDomain_injOn _ _) (coordinateOrthogonalAverageNN G)]
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hs] with z hz
      rw [jointExponentialCoordinates_abs_det_separated z hz.1,
        coordinateOrthogonalAverageNN_jointExponentialCoordinates]

end ResearchMain.WishartBlocks.Weyl
