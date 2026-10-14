import MainTheorems.DiagonalSchatten.OrderedPowerDuality

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem unorderedSpectralMatrix_power {l u theta q : ℝ}
    (hlu : l ≠ u) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) :
    symmetricPower r (orderedSpectralMatrix l u theta q) =
      orderedSpectralMatrix (l ^ r) (u ^ r) theta q := by
  rcases lt_or_gt_of_ne hlu with hlu | hlu
  · exact orderedSpectralMatrix_power hlu hq r
  · have hq' : (-q) ^ 2 = (1 - theta) * (1 - (1 - theta)) := by
      rw [neg_sq, hq]
      ring
    rw [orderedSpectralMatrix_swap, orderedSpectralMatrix_power hlu hq']
    exact (orderedSpectralMatrix_swap (l ^ r) (u ^ r) theta q).symm

theorem symmetricPower_inverse {r : ℝ} (hr : r ≠ 0) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    symmetricPower (1 / r) (symmetricPower r m) = m := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hu := (symmetricEigenvalues_positive hm hdet).2
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hq := symmetricEigenCoordinates_relation m hc
  have hn : symmetricMinus m ^ r ≠ symmetricPlus m ^ r := by
    intro he
    exact (ne_of_lt hlu) ((Real.rpow_left_inj hl.le hu.le hr).mp he)
  conv_lhs => rw [← symmetricSpectralRepresentation m hc]
  rw [orderedSpectralMatrix_power hlu hq, unorderedSpectralMatrix_power hn hq]
  have hroot {t : ℝ} (ht : 0 < t) : (t ^ r) ^ (1 / r) = t := by
    rw [← Real.rpow_mul ht.le, show r * (1 / r) = 1 by field_simp [hr], Real.rpow_one]
  rw [hroot hl, hroot hu, symmetricSpectralRepresentation m hc]

end

end ResearchMain.DiagonalSchatten
