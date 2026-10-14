import MainTheorems.WishartBlocks.SpectralLaw.Weyl.ExponentialChart
import Mathlib.MeasureTheory.Function.Jacobian

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory
open scoped Matrix.Norms.Operator

theorem exponentialMatrix_differentiable (n : ℕ) :
    Differentiable ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) := by
  intro W
  apply AnalyticAt.differentiableAt
  apply NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) W
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

theorem exponentialSpectralCoordinates_differentiable {n : ℕ} (lam : Fin n → ℝ) :
    Differentiable ℝ (exponentialSpectralCoordinates lam) := by
  have hpos : Differentiable ℝ (exponentialOrthogonalMatrix (n := n)) := by
    exact (exponentialMatrix_differentiable n).comp (skewContinuousLinearMap n).differentiable
  have hneg : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      NormedSpace.exp (-skewMatrix z)) := by
    exact (exponentialMatrix_differentiable n).comp
      (-skewContinuousLinearMap n).differentiable
  have hdiag : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      Matrix.diagonal lam + Matrix.diagonal (diagonalCoordinates z)) := by
    exact (diagonalContinuousLinearMap n).differentiable.const_add _
  exact (lowerContinuousLinearMap n).differentiable.comp ((hpos.mul hdiag).mul hneg)

theorem exponentialSpectralCoordinates_abs_det_fderiv_zero {n : ℕ}
    {lam : Fin n → ℝ} (hlam : StrictMono lam) :
    |(fderiv ℝ (exponentialSpectralCoordinates lam) 0).det| = gapProduct lam := by
  rw [(exponentialSpectralCoordinates_hasStrictFDerivAt_zero lam).hasFDerivAt.fderiv]
  simpa only [LinearMap.det_toMatrix'] using spectralDerivative_abs_det hlam

theorem exponentialSpectralChart_integral {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam)
    (G : (LowerIndex n → ℝ) → ℝ) :
    (∫ W in (exponentialSpectralChart lam hlam).target, G W) =
      ∫ z in (exponentialSpectralChart lam hlam).source,
        |(fderiv ℝ (exponentialSpectralCoordinates lam) z).det| *
          G (exponentialSpectralCoordinates lam z) := by
  have h := integral_target_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure (LowerIndex n → ℝ)))
    (f := exponentialSpectralChart lam hlam)
    (f' := fun z => fderiv ℝ (exponentialSpectralCoordinates lam) z)
    (fun z _ => (exponentialSpectralCoordinates_differentiable lam z).hasFDerivAt) G
  simpa only [exponentialSpectralChart_apply, smul_eq_mul] using h

end ResearchMain.WishartBlocks.Weyl
