import MainTheorems.WishartBlocks.SpectralLaw.Weyl.AnglePatch
import MainTheorems.WishartBlocks.SpectralLaw.Weyl.SmoothGlobal

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix.Norms.Operator

theorem exponentialOrthogonalMatrix_differentiable (n : ℕ) :
    Differentiable ℝ (exponentialOrthogonalMatrix (n := n)) :=
  (exponentialMatrix_differentiable n).comp (skewContinuousLinearMap n).differentiable

noncomputable def angularVelocity {n : ℕ} (z : LowerIndex n → ℝ) :
    (LowerIndex n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ({ toFun h := (exponentialOrthogonalMatrix z).transpose *
       fderiv ℝ exponentialOrthogonalMatrix z h
     map_add' := by
       intro h k
       simp only [map_add, Matrix.mul_add]
     map_smul' := by
       intro c h
       simp only [map_smul, Matrix.mul_smul, RingHom.id_apply] } :
    (LowerIndex n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).toContinuousLinearMap

@[simp] theorem angularVelocity_apply {n : ℕ} (z h : LowerIndex n → ℝ) :
    angularVelocity z h = (exponentialOrthogonalMatrix z).transpose *
      fderiv ℝ exponentialOrthogonalMatrix z h := rfl

set_option backward.isDefEq.respectTransparency false in
theorem angularVelocity_transpose {n : ℕ} (z h : LowerIndex n → ℝ) :
    (angularVelocity z h).transpose = -angularVelocity z h := by
  have hQ := (exponentialOrthogonalMatrix_differentiable n z).hasFDerivAt
  have hQT := (transposeContinuousLinearMap n).hasFDerivAt.comp z hQ
  have hprod := hQT.mul' hQ
  have hfun : (⇑(transposeContinuousLinearMap n) ∘ exponentialOrthogonalMatrix *
      exponentialOrthogonalMatrix) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext w
    change (exponentialOrthogonalMatrix w).transpose * exponentialOrthogonalMatrix w = 1
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (exponentialOrthogonalMatrix_mem w)
  rw [hfun] at hprod
  have hzero := hprod.unique (hasFDerivAt_const (1 : Matrix (Fin n) (Fin n) ℝ) z)
  have hsum := congrArg (fun L : (LowerIndex n → ℝ) →L[ℝ]
    Matrix (Fin n) (Fin n) ℝ => L h) hzero
  change (exponentialOrthogonalMatrix z).transpose * fderiv ℝ exponentialOrthogonalMatrix z h +
    (fderiv ℝ exponentialOrthogonalMatrix z h).transpose * exponentialOrthogonalMatrix z = 0 at hsum
  rw [angularVelocity_apply, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_right hsum

theorem exponentialOrthogonalMatrix_fderiv_factor {n : ℕ}
    (z h : LowerIndex n → ℝ) :
    fderiv ℝ exponentialOrthogonalMatrix z h =
      exponentialOrthogonalMatrix z * angularVelocity z h := by
  rw [angularVelocity_apply, ← Matrix.mul_assoc,
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (exponentialOrthogonalMatrix_mem z), Matrix.one_mul]

noncomputable def angularDerivative {n : ℕ} (z : LowerIndex n → ℝ) :
    (LowerIndex n → ℝ) →L[ℝ] (LowerIndex n → ℝ) :=
  ({ toFun h := spectralParameters (diagonalCoordinates h)
       (symmetricCoordinates (angularVelocity z h))
     map_add' := by
       intro h k
       funext e
       simp only [spectralParameters, diagonalCoordinates, symmetricCoordinates,
         map_add, Pi.add_apply, Matrix.add_apply]
       split_ifs <;> rfl
     map_smul' := by
       intro c h
       funext e
       simp only [spectralParameters, diagonalCoordinates, symmetricCoordinates,
         map_smul, Pi.smul_apply, Matrix.smul_apply]
       split_ifs <;> rfl } :
    (LowerIndex n → ℝ) →ₗ[ℝ] (LowerIndex n → ℝ)).toContinuousLinearMap

@[simp] theorem angularDerivative_apply {n : ℕ} (z h : LowerIndex n → ℝ) :
    angularDerivative z h = spectralParameters (diagonalCoordinates h)
      (symmetricCoordinates (angularVelocity z h)) := rfl

@[simp] theorem diagonalCoordinates_angularDerivative {n : ℕ}
    (z h : LowerIndex n → ℝ) :
    diagonalCoordinates (angularDerivative z h) = diagonalCoordinates h :=
  diagonalCoordinates_spectralParameters _ _

@[simp] theorem skewMatrix_angularDerivative {n : ℕ} (z h : LowerIndex n → ℝ) :
    skewMatrix (angularDerivative z h) = angularVelocity z h := by
  rw [angularDerivative_apply, skewMatrix_spectralParameters,
    skewMatrix_coordinates (angularVelocity_transpose z h)]

@[simp] theorem angularVelocity_zero {n : ℕ} (h : LowerIndex n → ℝ) :
    angularVelocity 0 h = skewMatrix h := by
  rw [angularVelocity_apply,
    (exponentialOrthogonalMatrix_hasStrictFDerivAt_zero n).hasFDerivAt.fderiv,
    exponentialOrthogonalMatrix_zero, Matrix.transpose_one, Matrix.one_mul]
  rfl

@[simp] theorem angularDerivative_zero (n : ℕ) :
    angularDerivative (0 : LowerIndex n → ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext h e
  rw [angularDerivative_apply, angularVelocity_zero]
  by_cases he : e.val.1 = e.val.2
  · have hindex : (⟨toLex (e.val.2, e.val.2), le_refl _⟩ : LowerIndex n) = e :=
      Subtype.ext (Prod.ext he.symm rfl)
    simp [spectralParameters, diagonalCoordinates, he, hindex]
  · have hlt := lt_of_le_of_ne e.property (Ne.symm he)
    simp [spectralParameters, symmetricCoordinates, skewMatrix, he, hlt]

end ResearchMain.WishartBlocks.Weyl
