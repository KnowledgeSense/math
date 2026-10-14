import MainTheorems.AHOConstants.SpectralPowers
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem realPiFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (I → ℂ) IsSelfAdjoint := by
  let : ContinuousFunctionalCalculus ℂ (I → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  exact IsSelfAdjoint.instContinuousFunctionalCalculus

attribute [local instance] realPiFunctionalCalculus

noncomputable def realDiagonalHom : (I → ℂ) →⋆ₐ[ℂ] Matrix I I ℂ where
  toFun v := Matrix.diagonal v
  map_one' := by ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' v w := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    rfl
  map_zero' := by simp
  map_add' v w := by
    exact (Matrix.diagonal_add v w).symm
  commutes' r := rfl
  map_star' v := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

theorem realDiagonalHom_continuous : Continuous (realDiagonalHom (I := I)) :=
  realDiagonalHom.toAlgHom.toLinearMap.toContinuousLinearMap.continuous

omit [DecidableEq I] in
theorem real_cfc_rpow_pi (v : I → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    cfc (fun x : ℝ => x ^ r) (fun i => (v i : ℂ)) =
      fun i => ((v i ^ r : ℝ) : ℂ) := by
  have hv : IsSelfAdjoint (fun i => (v i : ℂ)) := by ext i; simp
  have hv' : ∀ i, IsSelfAdjoint (v i : ℂ) := fun i => by simp [IsSelfAdjoint]
  rw [cfc_map_pi (S := ℂ) (fun x : ℝ => x ^ r) (fun i => (v i : ℂ))
    (Real.continuous_rpow_const hr).continuousOn hv hv']
  funext i
  simpa using
    cfc_algebraMap (A := ℂ) (v i) (fun x : ℝ => x ^ r)

theorem spectralPower_real_diagonal (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    {r : ℝ} (hr : 0 ≤ r) :
    spectralPower (Matrix.diagonal (fun i => (v i : ℂ))) r =
      Matrix.diagonal (fun i => ((v i ^ r : ℝ) : ℂ)) := by
  have hD : (Matrix.diagonal (fun i => (v i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by change 0 ≤ (v i : ℂ); exact_mod_cast hv i)
  change (Matrix.diagonal (fun i => (v i : ℂ))) ^ r = _
  rw [CFC.rpow_eq_cfc_real hD.nonneg]
  have hself : IsSelfAdjoint (fun i => (v i : ℂ)) := by ext i; simp
  have h := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (realDiagonalHom (I := I))
    (fun x : ℝ => x ^ r) (fun i => (v i : ℂ)) (Real.continuous_rpow_const hr).continuousOn
    realDiagonalHom_continuous hself hD.isHermitian.isSelfAdjoint
  rw [real_cfc_rpow_pi v hr] at h
  exact h.symm

end ResearchMain.AHOConstants
