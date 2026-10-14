import MainTheorems.DiagonalSchatten.SymmetricPowerDifferential

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def symmetricMatrix (m : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m 0, m 2; m 2, m 1]

theorem exists_real_two_column_gram (a b c : ℝ) (ha : 0 < a)
    (hdet : 0 < a * b - c ^ 2) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      gramFirst X = a ∧ gramSecond X = b ∧ gramCross X = c := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hres : 0 ≤ b - c ^ 2 / a := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ ha).mpr
    nlinarith
  let X : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.sqrt a, 0; c / Real.sqrt a, Real.sqrt (b - c ^ 2 / a)]
  refine ⟨X, ?_, ?_, ?_⟩
  · simp [gramFirst, Fin.sum_univ_two, X, Real.sq_sqrt ha.le]
  · simp only [gramSecond, Fin.sum_univ_two]
    change (c / Real.sqrt a) ^ 2 + Real.sqrt (b - c ^ 2 / a) ^ 2 = b
    rw [div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hres]
    ring
  · simp only [gramCross, Fin.sum_univ_two]
    change Real.sqrt a * (c / Real.sqrt a) + 0 * Real.sqrt (b - c ^ 2 / a) = c
    simp only [zero_mul, add_zero]
    field_simp [hsa.ne']

theorem symmetricPower_actual {m : Fin 3 → ℝ} (r : ℝ)
    (ha : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    complexifyRows (symmetricMatrix (symmetricPower r m)) =
      ResearchMain.AHOConstants.spectralPower (complexifyRows (symmetricMatrix m)) r := by
  obtain ⟨X, hA, hB, hC⟩ := exists_real_two_column_gram (m 0) (m 1) (m 2) ha hdet
  have hcross : gramCross X ≠ 0 := by rw [hC]; exact hc
  have hdata : ![gramFirst X, gramSecond X, gramCross X] = m := by
    funext i
    fin_cases i <;> simp [hA, hB, hC]
  have hp : realGramPowerCoefficient r X = symmetricPower r m := by
    rw [← symmetricPower_gram, hdata]
  have hG : complexifyRows X * (complexifyRows X).conjTranspose =
      complexifyRows (symmetricMatrix m) := by
    rw [twoRow_gram, rowMass_complexify, rowMass_complexify, rowCross_complexify]
    change hermitianTwo (gramFirst X) (gramSecond X) (gramCross X : ℂ) = _
    rw [hA, hB, hC]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianTwo, complexifyRows, symmetricMatrix]
  have hleft : realGramPowerMatrix r X = symmetricMatrix (symmetricPower r m) := by
    unfold realGramPowerMatrix symmetricMatrix
    rw [hp]
  rw [← hleft, ← hG]
  exact realGramPowerMatrix_eq_spectralPower r X hcross

end

end ResearchMain.DiagonalSchatten
