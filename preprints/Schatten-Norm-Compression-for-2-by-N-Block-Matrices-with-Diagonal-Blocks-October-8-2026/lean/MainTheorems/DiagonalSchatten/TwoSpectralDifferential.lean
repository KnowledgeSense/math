import MainTheorems.DiagonalSchatten.OrderedSpectralDifferential

namespace ResearchMain.DiagonalSchatten

noncomputable section

def twoSpectralMatrix (t theta q : ℝ) : Fin 3 → ℝ :=
  orderedSpectralMatrix t 1 theta q

def twoSpectralWeights (r t : ℝ) : Fin 3 → ℝ :=
  ![r, r * t ^ (r - 1), (1 - t ^ r) / (1 - t)]

theorem spectralWeightedMap_swap (theta q : ℝ) (weights z : Fin 3 → ℝ) :
    spectralWeightedMap (1 - theta) (-q) ![weights 1, weights 0, weights 2] z =
      spectralWeightedMap theta q weights z := by
  funext i
  fin_cases i <;>
    simp [spectralWeightedMap, fromSpectralCoordinates, spectralCoordinates,
      Pi.mul_apply] <;> ring

theorem twoSpectralMatrix_swapped (t theta q : ℝ) :
    twoSpectralMatrix t theta q = orderedSpectralMatrix 1 t (1 - theta) (-q) := by
  funext i
  fin_cases i <;>
    simp [twoSpectralMatrix, orderedSpectralMatrix] <;> ring

theorem twoSpectralMatrix_power_variation {t theta q : ℝ}
    (ht1 : t ≠ 1) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) (z : Fin 3 → ℝ) :
    symmetricPowerVariation r (twoSpectralMatrix t theta q) z =
      spectralWeightedMap theta q (twoSpectralWeights r t) z := by
  rcases lt_or_gt_of_ne ht1 with ht1 | ht1
  · have h := orderedSpectralMatrix_power_variation ht1 hq r z
    simpa only [twoSpectralMatrix, orderedSpectralWeights, twoSpectralWeights,
      Real.one_rpow, mul_one] using h
  · have hq' : (-q) ^ 2 = (1 - theta) * (1 - (1 - theta)) := by
      rw [neg_sq, hq]
      ring
    rw [twoSpectralMatrix_swapped, orderedSpectralMatrix_power_variation ht1 hq']
    have hw : orderedSpectralWeights r 1 t =
        ![twoSpectralWeights r t 1, twoSpectralWeights r t 0,
          twoSpectralWeights r t 2] := by
      funext i
      fin_cases i <;>
        simp [orderedSpectralWeights, twoSpectralWeights]
      field_simp [(sub_pos.mpr ht1).ne', (sub_neg.mpr ht1).ne]
      ring
    rw [hw, spectralWeightedMap_swap]

theorem twoSpectralMatrix_power {t theta q : ℝ}
    (ht1 : t ≠ 1) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) :
    symmetricPower r (twoSpectralMatrix t theta q) = twoSpectralMatrix (t ^ r) theta q := by
  rcases lt_or_gt_of_ne ht1 with ht1 | ht1
  · obtain ⟨hp, hm⟩ := orderedSpectralMatrix_spectrum ht1 hq
    change symmetricPower r (orderedSpectralMatrix t 1 theta q) =
      orderedSpectralMatrix (t ^ r) 1 theta q
    unfold symmetricPower symmetricDividedPower
    rw [orderedSpectralMatrix_gap ht1 hq, hp, hm]
    funext i
    fin_cases i <;>
      simp [orderedSpectralMatrix] <;>
      field_simp [(sub_pos.mpr ht1).ne']
  · have hq' : (-q) ^ 2 = (1 - theta) * (1 - (1 - theta)) := by
      rw [neg_sq, hq]
      ring
    rw [twoSpectralMatrix_swapped]
    obtain ⟨hp, hm⟩ := orderedSpectralMatrix_spectrum ht1 hq'
    unfold symmetricPower symmetricDividedPower
    rw [orderedSpectralMatrix_gap ht1 hq', hp, hm]
    funext i
    fin_cases i <;>
      simp [twoSpectralMatrix, orderedSpectralMatrix] <;>
      field_simp [(sub_pos.mpr ht1).ne'] <;> ring

theorem twoSpectralWeights_positive {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ht1 : t ≠ 1) :
    ∀ i, 0 < twoSpectralWeights r t i := by
  intro i
  fin_cases i
  · exact hr
  · exact mul_pos hr (Real.rpow_pos_of_pos ht _)
  · change 0 < (1 - t ^ r) / (1 - t)
    rcases lt_or_gt_of_ne ht1 with ht1 | ht1
    · exact div_pos (sub_pos.mpr (Real.rpow_lt_one ht.le ht1 hr)) (sub_pos.mpr ht1)
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (Real.one_lt_rpow ht1 hr)) (sub_neg.mpr ht1)

theorem twoSpectralWeights_negative {r t : ℝ} (hr : r < 0) (ht : 0 < t) (ht1 : t ≠ 1) :
    ∀ i, twoSpectralWeights r t i < 0 := by
  intro i
  fin_cases i
  · exact hr
  · exact mul_neg_of_neg_of_pos hr (Real.rpow_pos_of_pos ht _)
  · change (1 - t ^ r) / (1 - t) < 0
    rcases lt_or_gt_of_ne ht1 with ht1 | ht1
    · exact div_neg_of_neg_of_pos
        (sub_neg.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht ht1 hr)) (sub_pos.mpr ht1)
    · have hp : t ^ r < 1 := Real.rpow_lt_one_of_one_lt_of_neg ht1 hr
      exact div_neg_of_pos_of_neg (sub_pos.mpr hp) (sub_neg.mpr ht1)

end

end ResearchMain.DiagonalSchatten
