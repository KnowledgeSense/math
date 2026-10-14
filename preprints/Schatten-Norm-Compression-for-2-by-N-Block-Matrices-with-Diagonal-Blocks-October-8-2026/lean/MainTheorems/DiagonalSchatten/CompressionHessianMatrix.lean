import MainTheorems.DiagonalSchatten.ColumnExchange
import MainTheorems.DiagonalSchatten.ChartHessianValues
import MainTheorems.DiagonalSchatten.RadialPrincipalMinor
import MainTheorems.DiagonalSchatten.DefiniteContinuation

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def matrixCoordinateUnit (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℝ :=
  matrixFromCoordinates (Pi.single j 1)

theorem matrixFromCoordinates_eq_sum (e : Fin 4 → ℝ) :
    matrixFromCoordinates e = ∑ j, e j • matrixCoordinateUnit j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixFromCoordinates, matrixCoordinateUnit, Fin.sum_univ_succ]

theorem matrixFromCoordinates_matrixCoordinates (E : Matrix (Fin 2) (Fin 2) ℝ) :
    matrixFromCoordinates (matrixCoordinates E) = E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixFromCoordinates, matrixCoordinates]

def compressionHessianMatrix (p : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => compressionHessian p B (matrixCoordinateUnit j) (matrixCoordinateUnit i)

theorem compressionHessianMatrix_mulVec (p : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (e : Fin 4 → ℝ) :
    (compressionHessianMatrix p B).mulVec e =
      fun i => compressionHessian p B (matrixFromCoordinates e) (matrixCoordinateUnit i) := by
  ext i
  rw [matrixFromCoordinates_eq_sum]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, compressionHessianMatrix,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem compressionHessianMatrix_kernel_iff (p : ℝ)
    (B E : Matrix (Fin 2) (Fin 2) ℝ) :
    (compressionHessianMatrix p B).mulVec (matrixCoordinates E) = 0 ↔
      compressionHessian p B E = 0 := by
  rw [compressionHessianMatrix_mulVec, matrixFromCoordinates_matrixCoordinates]
  constructor
  · intro h
    ext F
    rw [← matrixFromCoordinates_matrixCoordinates F, matrixFromCoordinates_eq_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    have hi : ∀ j, compressionHessian p B E (matrixCoordinateUnit j) = 0 :=
      fun j => congrFun h j
    simp only [hi, mul_zero, Finset.sum_const_zero, zero_apply]
  · intro h
    simp only [h, zero_apply, Pi.zero_def]

theorem compressionHessianMatrix_quadratic (p : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (e : Fin 4 → ℝ) :
    dotProduct (star e) ((compressionHessianMatrix p B).mulVec e) =
      compressionHessian p B (matrixFromCoordinates e) (matrixFromCoordinates e) := by
  rw [compressionHessianMatrix_mulVec]
  have he := congrArg (fun F => compressionHessian p B (matrixFromCoordinates e) F)
    (matrixFromCoordinates_eq_sum e)
  rw [he]
  simp only [dotProduct, Pi.star_apply, star_trivial, map_sum, map_smul, smul_eq_mul]

theorem radialPrincipalMinor_quadratic (A : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 3 → ℝ) :
    dotProduct (star v) ((radialPrincipalMinor A).mulVec v) =
      dotProduct (star (principalExtension v)) (A.mulVec (principalExtension v)) := by
  simp [dotProduct, Matrix.mulVec, radialPrincipalMinor, principalExtension,
    Fin.sum_univ_succ]

theorem compressionHessianMatrix_symmetric {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    ∀ i j, compressionHessianMatrix p B i j = compressionHessianMatrix p B j i := by
  intro i j
  exact compressionHessian_symmetric hp B hB hdet _ _

theorem compressionHessian_principal_det_ne_zero {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : (realEntryRoot p B).det ≠ 0) :
    (radialPrincipalMinor (compressionHessianMatrix p B)).det ≠ 0 := by
  have hp0 : 0 < p := by linarith
  have hgram : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2 := by
    rw [twoByTwo_gramDet_eq_det_sq]
    exact sq_pos_of_ne_zero hdet
  apply radialPrincipalMinor_det_ne_zero
    (compressionHessianMatrix_symmetric hp0 B hB hgram) (matrixCoordinates B)
    (by simpa [matrixCoordinates] using (hB 0 0).ne')
  · apply (compressionHessianMatrix_kernel_iff p B B).mpr
    exact compressionHessian_radial_zero hp B hB hgram
  · intro e he
    have hE : compressionHessian p B (matrixFromCoordinates e) = 0 := by
      apply (compressionHessianMatrix_kernel_iff p B (matrixFromCoordinates e)).mp
      simpa only [matrixCoordinates_matrixFromCoordinates] using he
    obtain ⟨r, hr⟩ := compressionHessian_two_column_kernel hp hp2 B hB hdet
      (matrixFromCoordinates e) hE
    refine ⟨r, ?_⟩
    have h := congrArg matrixCoordinates hr
    rw [matrixCoordinates_matrixFromCoordinates] at h
    simpa [matrixCoordinates, Pi.smul_apply, smul_eq_mul] using h

end

end ResearchMain.DiagonalSchatten
