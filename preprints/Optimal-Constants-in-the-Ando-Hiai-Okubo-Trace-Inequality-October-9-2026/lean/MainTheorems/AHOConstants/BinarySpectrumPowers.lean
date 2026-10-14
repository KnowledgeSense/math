import MainTheorems.AHOConstants.MatrixFunctionalCalculus

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem binarySpectrum_spectralPower {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.PosSemidef) {l u : ℝ} (hlu : l ≠ u)
    (hs : ∀ x ∈ spectrum ℝ A, x = l ∨ x = u) (p : ℝ) :
    spectralPower A p = l ^ p • (1 : Matrix I I ℂ) +
      ((u ^ p - l ^ p) / (u - l)) • (A - l • (1 : Matrix I I ℂ)) := by
  let c := (u ^ p - l ^ p) / (u - l)
  have hden : u - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlu)
  have he : cfc (fun x : ℝ => x ^ p) A =
      cfc (fun x : ℝ => l ^ p + c * (x - l)) A := by
    apply cfc_congr
    intro x hx
    rcases hs x hx with rfl | rfl
    · simp
    · dsimp [c]
      field_simp [hden]
      ring
  change A ^ p = _
  rw [CFC.rpow_eq_cfc_real hA.nonneg, he, matrix_cfc_add, matrix_cfc_const_mul, matrix_cfc_sub,
    cfc_id' ℝ A hA.isHermitian.isSelfAdjoint,
    cfc_const (l ^ p) A hA.isHermitian.isSelfAdjoint,
    cfc_const l A hA.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]

end ResearchMain.AHOConstants
