import MainTheorems.DiagonalSchatten.TwoRowDifferential
import MainTheorems.DiagonalSchatten.TwoSpectrumPower

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

variable {J : Type*} [Fintype J]

def realGramPowerMatrix (r : ℝ) (X : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![realGramPowerCoefficient r X 0, realGramPowerCoefficient r X 2;
    realGramPowerCoefficient r X 2, realGramPowerCoefficient r X 1]

theorem realGramGap_eq_eigenvalue_difference (X : Matrix (Fin 2) J ℝ) :
    realGramPlus X - realGramMinus X = realGramGap X := by
  unfold realGramPlus realGramMinus realGramGap
  ring

theorem realGramPowerMatrix_eq_spectralPower (r : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hc : gramCross X ≠ 0) :
    complexifyRows (realGramPowerMatrix r X) =
      ResearchMain.AHOConstants.spectralPower
        (complexifyRows X * (complexifyRows X).conjTranspose) r := by
  have hgap : twoEigenvalueGap (rowMass (complexifyRows X) 0)
      (rowMass (complexifyRows X) 1) (rowCross (complexifyRows X)) = realGramGap X := by
    rw [rowMass_complexify, rowMass_complexify, rowCross_complexify]
    simp [twoEigenvalueGap, realGramGap, gramFirst, gramSecond,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : 0 < twoEigenvalueGap (rowMass (complexifyRows X) 0)
      (rowMass (complexifyRows X) 1) (rowCross (complexifyRows X)) := by
    rw [hgap]
    exact realGramGap_positive X hc
  rw [rowGram_spectralPower _ r hp]
  have hplus : twoEigenvaluePlus (rowMass (complexifyRows X) 0)
      (rowMass (complexifyRows X) 1) (rowCross (complexifyRows X)) = realGramPlus X := by
    rw [rowMass_complexify, rowMass_complexify, rowCross_complexify]
    simpa only [gramFirst, gramSecond] using (realGramPlus_eq X).symm
  have hminus : twoEigenvalueMinus (rowMass (complexifyRows X) 0)
      (rowMass (complexifyRows X) 1) (rowCross (complexifyRows X)) = realGramMinus X := by
    rw [rowMass_complexify, rowMass_complexify, rowCross_complexify]
    simpa only [gramFirst, gramSecond] using (realGramMinus_eq X).symm
  rw [hplus, hminus, realGramGap_eq_eigenvalue_difference]
  have hG : complexifyRows X * (complexifyRows X).conjTranspose =
      hermitianTwo (gramFirst X) (gramSecond X) (gramCross X : ℂ) := by
    rw [twoRow_gram, rowMass_complexify, rowMass_complexify, rowCross_complexify]
    rfl
  rw [hG]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyRows, realGramPowerMatrix, realGramPowerCoefficient, hermitianTwo,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]

end

end ResearchMain.DiagonalSchatten
