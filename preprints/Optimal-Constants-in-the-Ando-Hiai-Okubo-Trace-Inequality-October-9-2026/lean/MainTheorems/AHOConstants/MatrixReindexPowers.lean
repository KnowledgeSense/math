import MainTheorems.AHOConstants.ConjugationPowers
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def matrixReindexStarAlgEquiv (e : I ≃ J) :
    Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by intro A; ext i j; rfl)

theorem matrixReindex_posSemidef (e : I ≃ J) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (matrixReindexStarAlgEquiv e A).PosSemidef := hA.submatrix e.symm

theorem matrixReindex_realEntries (e : I ≃ J) {A : Matrix I I ℂ}
    (hreal : ∀ i j, (A i j).im = 0) :
    ∀ i j, (matrixReindexStarAlgEquiv e A i j).im = 0 := by
  intro i j
  exact hreal (e.symm i) (e.symm j)

theorem matrixReindex_trace (e : I ≃ J) (A : Matrix I I ℂ) :
    Matrix.trace (matrixReindexStarAlgEquiv e A) = Matrix.trace A :=
  Equiv.sum_comp e.symm (fun i => A i i)

theorem matrixReindex_spectralPower (e : I ≃ J) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (r : ℝ) :
    spectralPower (matrixReindexStarAlgEquiv e A) r =
      matrixReindexStarAlgEquiv e (spectralPower A r) := by
  let φ := matrixReindexStarAlgEquiv e
  have hP := matrixReindex_posSemidef e hA
  change (φ A) ^ r = φ (A ^ r)
  rw [CFC.rpow_eq_cfc_real hP.nonneg, CFC.rpow_eq_cfc_real hA.nonneg]
  exact (StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ (fun x : ℝ => x ^ r) A
    ((Matrix.finite_real_spectrum (A := A)).continuousOn _)
    φ.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap.continuous
    hA.isHermitian.isSelfAdjoint hP.isHermitian.isSelfAdjoint).symm

theorem matrixReindex_word (e : I ≃ J) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (w : TraceWord) :
    matrixWord (matrixReindexStarAlgEquiv e A) (matrixReindexStarAlgEquiv e B) w =
      matrixReindexStarAlgEquiv e (matrixWord A B w) := by
  let φ := matrixReindexStarAlgEquiv e
  induction w with
  | nil => exact (map_one φ).symm
  | cons cr w ih =>
    rw [matrixWord_cons, matrixWord_cons, map_mul, ih]
    cases hc : cr.1
    · simp only [Bool.false_eq_true, ite_false]
      rw [matrixReindex_spectralPower e hB]
    · simp only [ite_true]
      rw [matrixReindex_spectralPower e hA]

theorem matrixReindex_wordTrace (e : I ≃ J) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (w : TraceWord) :
    wordTrace (matrixReindexStarAlgEquiv e A) (matrixReindexStarAlgEquiv e B) w =
      wordTrace A B w := by
  unfold wordTrace
  rw [matrixReindex_word e hA hB, matrixReindex_trace]

end ResearchMain.AHOConstants
