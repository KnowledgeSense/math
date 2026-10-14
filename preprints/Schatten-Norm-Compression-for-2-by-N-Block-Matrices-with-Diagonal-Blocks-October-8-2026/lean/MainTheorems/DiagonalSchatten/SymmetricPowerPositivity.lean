import MainTheorems.DiagonalSchatten.OrderedPowerDuality

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem orderedSpectralMatrix_determinant (l u theta q : ℝ)
    (hq : q ^ 2 = theta * (1 - theta)) :
    orderedSpectralMatrix l u theta q 0 * orderedSpectralMatrix l u theta q 1 -
      orderedSpectralMatrix l u theta q 2 ^ 2 = l * u := by
  simp [orderedSpectralMatrix]
  linear_combination -(u - l) ^ 2 * hq

theorem orderedSpectralMatrix_first_pos {l u theta q : ℝ}
    (hl : 0 < l) (hu : 0 < u) (ht0 : 0 < theta) (ht1 : theta < 1) :
    0 < orderedSpectralMatrix l u theta q 0 := by
  change 0 < l + (u - l) * theta
  have he : l + (u - l) * theta = l * (1 - theta) + u * theta := by ring
  rw [he]
  exact add_pos (mul_pos hl (sub_pos.mpr ht1)) (mul_pos hu ht0)

theorem orderedSpectralMatrix_second_pos {l u theta q : ℝ}
    (hl : 0 < l) (hu : 0 < u) (ht0 : 0 < theta) (ht1 : theta < 1) :
    0 < orderedSpectralMatrix l u theta q 1 := by
  change 0 < l + (u - l) * (1 - theta)
  have he : l + (u - l) * (1 - theta) = l * theta + u * (1 - theta) := by ring
  rw [he]
  exact add_pos (mul_pos hl ht0) (mul_pos hu (sub_pos.mpr ht1))

theorem symmetricPower_positive_definite (r : ℝ) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    0 < symmetricPower r m 0 ∧ 0 < symmetricPower r m 1 ∧
      0 < symmetricPower r m 0 * symmetricPower r m 1 - symmetricPower r m 2 ^ 2 := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hu := (symmetricEigenvalues_positive hm hdet).2
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  obtain ⟨ht0, ht1⟩ := symmetricEigenCoordinates_bounds m hc
  have hq := symmetricEigenCoordinates_relation m hc
  rw [← symmetricSpectralRepresentation m hc, orderedSpectralMatrix_power hlu hq]
  refine ⟨orderedSpectralMatrix_first_pos (Real.rpow_pos_of_pos hl r)
    (Real.rpow_pos_of_pos hu r) ht0 ht1,
    orderedSpectralMatrix_second_pos (Real.rpow_pos_of_pos hl r)
      (Real.rpow_pos_of_pos hu r) ht0 ht1, ?_⟩
  rw [orderedSpectralMatrix_determinant _ _ _ _ hq]
  exact mul_pos (Real.rpow_pos_of_pos hl r) (Real.rpow_pos_of_pos hu r)

theorem symmetricPower_cross_positive {r : ℝ} (hr : 0 < r) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : 0 < m 2) :
    0 < symmetricPower r m 2 := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc.ne'
  have hq := symmetricEigenCoordinates_relation m hc.ne'
  have hqp : 0 < symmetricEigenCross m := div_pos hc (symmetricGap_positive m hc.ne')
  rw [← symmetricSpectralRepresentation m hc.ne', orderedSpectralMatrix_power hlu hq]
  change 0 < (symmetricPlus m ^ r - symmetricMinus m ^ r) * symmetricEigenCross m
  exact mul_pos (sub_pos.mpr (Real.rpow_lt_rpow hl.le hlu hr)) hqp

theorem symmetricPower_cross_negative {r : ℝ} (hr : r < 0) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : 0 < m 2) :
    symmetricPower r m 2 < 0 := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc.ne'
  have hq := symmetricEigenCoordinates_relation m hc.ne'
  have hqp : 0 < symmetricEigenCross m := div_pos hc (symmetricGap_positive m hc.ne')
  rw [← symmetricSpectralRepresentation m hc.ne', orderedSpectralMatrix_power hlu hq]
  change (symmetricPlus m ^ r - symmetricMinus m ^ r) * symmetricEigenCross m < 0
  exact mul_neg_of_neg_of_pos (sub_neg.mpr (Real.rpow_lt_rpow_of_neg hl hlu hr)) hqp

end

end ResearchMain.DiagonalSchatten
