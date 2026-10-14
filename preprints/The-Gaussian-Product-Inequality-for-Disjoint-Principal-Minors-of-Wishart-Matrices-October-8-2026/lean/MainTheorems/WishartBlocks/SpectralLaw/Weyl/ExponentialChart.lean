import MainTheorems.WishartBlocks.SpectralLaw.Weyl.Coordinates
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ResearchMain.WishartBlocks.Weyl

open scoped Matrix.Norms.Operator

noncomputable def skewContinuousLinearMap (n : ℕ) :
    (LowerIndex n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (skewLinearMap n).toContinuousLinearMap

noncomputable def diagonalContinuousLinearMap (n : ℕ) :
    (LowerIndex n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (diagonalLinearMap n).toContinuousLinearMap

noncomputable def lowerContinuousLinearMap (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (LowerIndex n → ℝ) :=
  (lowerLinearMap n).toContinuousLinearMap

noncomputable def exponentialOrthogonalMatrix {n : ℕ} (z : LowerIndex n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp (skewMatrix z)

theorem exponentialOrthogonalMatrix_mem {n : ℕ} (z : LowerIndex n → ℝ) :
    exponentialOrthogonalMatrix z ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
  change NormedSpace.exp (skewMatrix z) * (NormedSpace.exp (skewMatrix z)).transpose = 1
  have hcomm : Commute (skewMatrix z) (-skewMatrix z) :=
    (Commute.refl (skewMatrix z)).neg_right
  rw [← Matrix.exp_transpose, skewMatrix_transpose,
    ← Matrix.exp_add_of_commute _ _ hcomm,
    add_neg_cancel, NormedSpace.exp_zero]

@[simp] theorem exponentialOrthogonalMatrix_zero (n : ℕ) :
    exponentialOrthogonalMatrix (0 : LowerIndex n → ℝ) = 1 := by
  simp [exponentialOrthogonalMatrix]

theorem exponentialOrthogonalMatrix_transpose {n : ℕ} (z : LowerIndex n → ℝ) :
    (exponentialOrthogonalMatrix z).transpose = NormedSpace.exp (-skewMatrix z) := by
  rw [exponentialOrthogonalMatrix, ← Matrix.exp_transpose, skewMatrix_transpose]

noncomputable def exponentialSpectralMatrix {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  exponentialOrthogonalMatrix z *
    (Matrix.diagonal lam + Matrix.diagonal (diagonalCoordinates z)) *
      NormedSpace.exp (-skewMatrix z)

noncomputable def exponentialSpectralCoordinates {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) : LowerIndex n → ℝ :=
  symmetricCoordinates (exponentialSpectralMatrix lam z)

theorem exponentialSpectralMatrix_eq_congruence {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    exponentialSpectralMatrix lam z = exponentialOrthogonalMatrix z *
      Matrix.diagonal (lam + diagonalCoordinates z) *
        (exponentialOrthogonalMatrix z).transpose := by
  rw [exponentialSpectralMatrix, Pi.add_def, Matrix.diagonal_add,
    exponentialOrthogonalMatrix_transpose]

theorem exponentialSpectralMatrix_isHermitian {n : ℕ}
    (lam : Fin n → ℝ) (z : LowerIndex n → ℝ) :
    (exponentialSpectralMatrix lam z).IsHermitian := by
  rw [exponentialSpectralMatrix_eq_congruence]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose (exponentialOrthogonalMatrix z)
      (Matrix.isHermitian_diagonal (lam + diagonalCoordinates z))

@[simp] theorem exponentialSpectralCoordinates_zero {n : ℕ} (lam : Fin n → ℝ) :
    exponentialSpectralCoordinates lam 0 = symmetricCoordinates (Matrix.diagonal lam) := by
  simp [exponentialSpectralCoordinates, exponentialSpectralMatrix,
    diagonalCoordinates, skewMatrix_zero]

set_option backward.isDefEq.respectTransparency false in
theorem exponentialOrthogonalMatrix_hasStrictFDerivAt_zero (n : ℕ) :
    HasStrictFDerivAt exponentialOrthogonalMatrix (skewContinuousLinearMap n)
      (0 : LowerIndex n → ℝ) := by
  have hexp : HasStrictFDerivAt NormedSpace.exp
      (1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
      ((skewContinuousLinearMap n) 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
      (𝔸 := Matrix (Fin n) (Fin n) ℝ))
  have h := hexp.comp (0 : LowerIndex n → ℝ)
    (skewContinuousLinearMap n).hasStrictFDerivAt
  convert h using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem exponentialSpectralCoordinates_hasStrictFDerivAt_zero {n : ℕ}
    (lam : Fin n → ℝ) :
    HasStrictFDerivAt (exponentialSpectralCoordinates lam) (spectralDerivative lam)
      (0 : LowerIndex n → ℝ) := by
  have hpos := exponentialOrthogonalMatrix_hasStrictFDerivAt_zero n
  have hneg : HasStrictFDerivAt (fun z : LowerIndex n → ℝ =>
      NormedSpace.exp (-skewMatrix z)) (-skewContinuousLinearMap n) 0 := by
    have hexp : HasStrictFDerivAt NormedSpace.exp
        (1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
        ((-skewContinuousLinearMap n) 0) := by
      simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
        (𝔸 := Matrix (Fin n) (Fin n) ℝ))
    have h := hexp.comp (0 : LowerIndex n → ℝ)
      (-skewContinuousLinearMap n).hasStrictFDerivAt
    convert h using 1 <;> rfl
  have hdiag := ((diagonalContinuousLinearMap n).hasStrictFDerivAt (x := 0)).const_add
    (Matrix.diagonal lam)
  have h := (lowerContinuousLinearMap n).hasStrictFDerivAt.comp
    (0 : LowerIndex n → ℝ) ((hpos.mul' hdiag).mul' hneg)
  convert h using 1
  · rfl
  · ext z e
    simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, neg_apply,
      Pi.mul_apply, exponentialOrthogonalMatrix_zero, map_zero, add_zero,
      skewMatrix_zero, neg_zero, NormedSpace.exp_zero,
      smul_eq_mul, op_smul_eq_mul, Matrix.one_mul, Matrix.mul_one]
    change spectralDerivative lam z e =
      symmetricCoordinates (Matrix.diagonal lam * (-skewMatrix z) +
        (Matrix.diagonal (diagonalCoordinates z) + skewMatrix z * Matrix.diagonal lam)) e
    have hmatrix : Matrix.diagonal lam * (-skewMatrix z) +
        (Matrix.diagonal (diagonalCoordinates z) + skewMatrix z * Matrix.diagonal lam) =
        tangentMatrix lam z := by
      simp only [tangentMatrix, Matrix.mul_neg]
      abel
    rw [hmatrix]
    exact congrFun (tangentMatrix_coordinates lam z).symm e

noncomputable def spectralDerivativeEquiv {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Function.Injective lam) :
    (LowerIndex n → ℝ) ≃L[ℝ] (LowerIndex n → ℝ) :=
  (spectralDerivative lam).toContinuousLinearEquivOfDetNeZero (by
    simpa only [LinearMap.det_toMatrix'] using spectralDerivative_det_ne_zero hlam)

@[simp] theorem spectralDerivativeEquiv_toContinuousLinearMap {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    (spectralDerivativeEquiv lam hlam).toContinuousLinearMap = spectralDerivative lam :=
  ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _

noncomputable def exponentialSpectralChart {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    OpenPartialHomeomorph (LowerIndex n → ℝ) (LowerIndex n → ℝ) :=
  (show HasStrictFDerivAt (exponentialSpectralCoordinates lam)
    (spectralDerivativeEquiv lam hlam).toContinuousLinearMap 0 by
      simpa only [spectralDerivativeEquiv_toContinuousLinearMap] using
        exponentialSpectralCoordinates_hasStrictFDerivAt_zero lam).toOpenPartialHomeomorph _

@[simp] theorem exponentialSpectralChart_apply {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) (z : LowerIndex n → ℝ) :
    exponentialSpectralChart lam hlam z = exponentialSpectralCoordinates lam z := rfl

theorem exponentialSpectralChart_zero_mem_source {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    (0 : LowerIndex n → ℝ) ∈ (exponentialSpectralChart lam hlam).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

theorem exponentialSpectralChart_diagonal_mem_target {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    symmetricCoordinates (Matrix.diagonal lam) ∈ (exponentialSpectralChart lam hlam).target := by
  simpa only [exponentialSpectralChart_apply, exponentialSpectralCoordinates_zero] using
    (exponentialSpectralChart lam hlam).map_source
      (exponentialSpectralChart_zero_mem_source lam hlam)

end ResearchMain.WishartBlocks.Weyl
