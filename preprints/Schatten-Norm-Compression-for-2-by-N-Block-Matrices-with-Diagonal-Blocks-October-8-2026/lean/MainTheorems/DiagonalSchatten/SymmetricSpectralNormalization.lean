import MainTheorems.DiagonalSchatten.TwoSpectralDifferential

namespace ResearchMain.DiagonalSchatten

noncomputable section

def symmetricTheta (m : Fin 3 → ℝ) : ℝ :=
  (m 0 - symmetricMinus m) / symmetricGap m

def symmetricEigenCross (m : Fin 3 → ℝ) : ℝ := m 2 / symmetricGap m

theorem symmetricGap_square (m : Fin 3 → ℝ) :
    symmetricGap m ^ 2 = (m 0 - m 1) ^ 2 + 4 * m 2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem symmetricEigenvalues_gap (m : Fin 3 → ℝ) :
    symmetricPlus m - symmetricMinus m = symmetricGap m := by
  unfold symmetricPlus symmetricMinus
  ring

theorem symmetricEigenvalues_product (m : Fin 3 → ℝ) :
    symmetricPlus m * symmetricMinus m = m 0 * m 1 - m 2 ^ 2 := by
  unfold symmetricPlus symmetricMinus
  nlinarith [symmetricGap_square m]

theorem symmetricEigenvalues_positive {m : Fin 3 → ℝ}
    (ha : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) :
    0 < symmetricMinus m ∧ 0 < symmetricPlus m := by
  have hb : 0 < m 1 := by nlinarith [sq_nonneg (m 2)]
  have hgap : 0 ≤ symmetricGap m := Real.sqrt_nonneg _
  have hs : 0 < m 0 + m 1 := add_pos ha hb
  have hg : symmetricGap m < m 0 + m 1 := by
    nlinarith [symmetricGap_square m]
  unfold symmetricMinus symmetricPlus
  constructor <;> linarith

theorem symmetricEigenCoordinates_relation (m : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    symmetricEigenCross m ^ 2 = symmetricTheta m * (1 - symmetricTheta m) := by
  have hg := (symmetricGap_positive m hc).ne'
  have hs := symmetricGap_square m
  unfold symmetricEigenCross symmetricTheta symmetricMinus
  field_simp [hg]
  nlinarith [hs]

theorem symmetricEigenCoordinates_bounds (m : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    0 < symmetricTheta m ∧ symmetricTheta m < 1 := by
  have hq : symmetricEigenCross m ≠ 0 := div_ne_zero hc (symmetricGap_positive m hc).ne'
  have hq2 := sq_pos_of_ne_zero hq
  rw [symmetricEigenCoordinates_relation m hc] at hq2
  constructor <;> nlinarith [sq_nonneg (symmetricTheta m)]

theorem symmetricSpectralRepresentation (m : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    orderedSpectralMatrix (symmetricMinus m) (symmetricPlus m)
      (symmetricTheta m) (symmetricEigenCross m) = m := by
  have hg := (symmetricGap_positive m hc).ne'
  unfold orderedSpectralMatrix
  rw [symmetricEigenvalues_gap]
  funext i
  fin_cases i
  · change symmetricMinus m + symmetricGap m *
      ((m 0 - symmetricMinus m) / symmetricGap m) = m 0
    field_simp [hg]
    ring
  · change symmetricMinus m + symmetricGap m *
      (1 - (m 0 - symmetricMinus m) / symmetricGap m) = m 1
    unfold symmetricMinus
    field_simp [hg]
    ring
  · change symmetricGap m * (m 2 / symmetricGap m) = m 2
    field_simp [hg]

theorem symmetricPowerVariation_spectral (r : ℝ) (m z : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    symmetricPowerVariation r m z =
      spectralWeightedMap (symmetricTheta m) (symmetricEigenCross m)
        (orderedSpectralWeights r (symmetricMinus m) (symmetricPlus m)) z := by
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have h := orderedSpectralMatrix_power_variation hlu (symmetricEigenCoordinates_relation m hc) r z
  rw [symmetricSpectralRepresentation m hc] at h
  exact h

end

end ResearchMain.DiagonalSchatten
