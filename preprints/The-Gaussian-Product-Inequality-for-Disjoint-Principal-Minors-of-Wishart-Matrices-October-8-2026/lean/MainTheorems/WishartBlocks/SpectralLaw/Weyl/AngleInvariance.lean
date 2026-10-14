import MainTheorems.WishartBlocks.SpectralLaw.Weyl.JacobianFactorization

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix.Norms.Operator

noncomputable def diagonalParameters {n : ℕ} (lam : Fin n → ℝ) : LowerIndex n → ℝ :=
  spectralParameters lam 0

@[simp] theorem skewMatrix_diagonalParameters {n : ℕ} (lam : Fin n → ℝ) :
    skewMatrix (diagonalParameters lam) = 0 := by
  rw [diagonalParameters, skewMatrix_spectralParameters, skewMatrix_zero]

theorem angleCoordinates_add_diagonalParameters {n : ℕ} (z : LowerIndex n → ℝ) :
    angleCoordinates z + diagonalParameters (diagonalCoordinates z) = z := by
  funext e
  by_cases he : e.val.1 = e.val.2
  · have hindex : (⟨toLex (e.val.2, e.val.2), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext he.symm rfl)
    simp [angleCoordinates, diagonalParameters, spectralParameters,
      diagonalCoordinates, he, hindex]
  · simp [angleCoordinates, diagonalParameters, spectralParameters, he]

@[simp] theorem exponentialOrthogonalMatrix_add_diagonalParameters {n : ℕ}
    (z : LowerIndex n → ℝ) (lam : Fin n → ℝ) :
    exponentialOrthogonalMatrix (z + diagonalParameters lam) = exponentialOrthogonalMatrix z := by
  have hskew : skewMatrix (z + diagonalParameters lam) = skewMatrix z := by
    rw [show skewMatrix (z + diagonalParameters lam) =
      skewMatrix z + skewMatrix (diagonalParameters lam) from (skewLinearMap n).map_add _ _,
      skewMatrix_diagonalParameters, add_zero]
  simp only [exponentialOrthogonalMatrix, hskew]

set_option backward.isDefEq.respectTransparency false in
theorem exponentialOrthogonalMatrix_fderiv_add_diagonalParameters {n : ℕ}
    (z : LowerIndex n → ℝ) (lam : Fin n → ℝ) :
    fderiv ℝ exponentialOrthogonalMatrix (z + diagonalParameters lam) =
      fderiv ℝ exponentialOrthogonalMatrix z := by
  have h := (exponentialOrthogonalMatrix_differentiable n
    (z + diagonalParameters lam)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (diagonalParameters lam))
  have hshift : HasFDerivAt exponentialOrthogonalMatrix
      (fderiv ℝ exponentialOrthogonalMatrix (z + diagonalParameters lam)) z := by
    simpa only [Function.comp_def, id_eq, exponentialOrthogonalMatrix_add_diagonalParameters,
      ContinuousLinearMap.comp_id] using h
  exact hshift.unique (exponentialOrthogonalMatrix_differentiable n z).hasFDerivAt

theorem exponentialOrthogonalMatrix_fderiv_angleCoordinates {n : ℕ}
    (z : LowerIndex n → ℝ) :
    fderiv ℝ exponentialOrthogonalMatrix z =
      fderiv ℝ exponentialOrthogonalMatrix (angleCoordinates z) := by
  have h := exponentialOrthogonalMatrix_fderiv_add_diagonalParameters
    (angleCoordinates z) (diagonalCoordinates z)
  rwa [angleCoordinates_add_diagonalParameters] at h

theorem angularVelocity_angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    angularVelocity (angleCoordinates z) = angularVelocity z := by
  have hQ : exponentialOrthogonalMatrix (angleCoordinates z) = exponentialOrthogonalMatrix z :=
    congrArg Subtype.val (exponentialOrthogonal_angleCoordinates z)
  ext h
  rw [angularVelocity_apply, angularVelocity_apply, hQ,
    ← exponentialOrthogonalMatrix_fderiv_angleCoordinates z]

theorem angularDerivative_angleCoordinates {n : ℕ} (z : LowerIndex n → ℝ) :
    angularDerivative (angleCoordinates z) = angularDerivative z := by
  ext h
  rw [angularDerivative_apply, angularDerivative_apply, angularVelocity_angleCoordinates]

theorem jointExponentialCoordinates_abs_det_separated {n : ℕ}
    (z : LowerIndex n → ℝ) (hz : StrictMono (diagonalCoordinates z)) :
    |(fderiv ℝ jointExponentialCoordinates z).det| =
      gapProduct (diagonalCoordinates z) * |(angularDerivative (angleCoordinates z)).det| := by
  rw [angularDerivative_angleCoordinates]
  exact jointExponentialCoordinates_abs_det z hz

end ResearchMain.WishartBlocks.Weyl
