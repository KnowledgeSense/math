import MainTheorems.WishartBlocks.SpectralLaw.Weyl.GlobalCoordinates
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.LocalChange

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix.Norms.Operator

noncomputable def transposeContinuousLinearMap (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ({ toFun := Matrix.transpose
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem cayleyOrthogonalMatrix_val_differentiable (n : ℕ) :
    Differentiable ℝ (fun z : LowerIndex n → ℝ => (cayleyOrthogonalMatrix z).val) := by
  have hskew : Differentiable ℝ (skewMatrix (n := n)) :=
    (skewContinuousLinearMap n).differentiable
  have hsub : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      (1 : Matrix (Fin n) (Fin n) ℝ) - skewMatrix z) := hskew.const_sub _
  have hinv : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      ((1 : Matrix (Fin n) (Fin n) ℝ) - skewMatrix z)⁻¹) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using hsub.inverse (fun z =>
      (Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr (one_sub_skew_det_ne_zero (skewMatrix_transpose z))))
  exact hinv.mul (hskew.const_add _)

theorem globalSpectralCoordinates_differentiable (n : ℕ) :
    Differentiable ℝ (globalSpectralCoordinates (n := n)) := by
  have hQ := cayleyOrthogonalMatrix_val_differentiable n
  have hQT : Differentiable ℝ (fun z : LowerIndex n → ℝ =>
      (cayleyOrthogonalMatrix z).val.transpose) :=
    (transposeContinuousLinearMap n).differentiable.comp hQ
  exact (lowerContinuousLinearMap n).differentiable.comp
    ((hQ.mul (diagonalContinuousLinearMap n).differentiable).mul hQT)

end ResearchMain.WishartBlocks.Weyl
