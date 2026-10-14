import MainTheorems.DiagonalSchatten.SymmetricSpectralNormalization

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem orderedSpectralMatrix_swap (l u theta q : ℝ) :
    orderedSpectralMatrix l u theta q = orderedSpectralMatrix u l (1 - theta) (-q) := by
  funext i
  fin_cases i <;>
    simp [orderedSpectralMatrix] <;> ring

theorem unorderedSpectralMatrix_power_variation {l u theta q : ℝ}
    (hlu : l ≠ u) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) (z : Fin 3 → ℝ) :
    symmetricPowerVariation r (orderedSpectralMatrix l u theta q) z =
      spectralWeightedMap theta q (orderedSpectralWeights r l u) z := by
  rcases lt_or_gt_of_ne hlu with hlu | hlu
  · exact orderedSpectralMatrix_power_variation hlu hq r z
  · have hq' : (-q) ^ 2 = (1 - theta) * (1 - (1 - theta)) := by
      rw [neg_sq, hq]
      ring
    rw [orderedSpectralMatrix_swap, orderedSpectralMatrix_power_variation hlu hq']
    have hw : orderedSpectralWeights r u l =
        ![orderedSpectralWeights r l u 1, orderedSpectralWeights r l u 0,
          orderedSpectralWeights r l u 2] := by
      funext i
      fin_cases i <;>
        simp [orderedSpectralWeights]
      field_simp [(sub_pos.mpr hlu).ne', (sub_neg.mpr hlu).ne]
      ring
    rw [hw, spectralWeightedMap_swap]

theorem orderedSpectralMatrix_power {l u theta q : ℝ}
    (hlu : l < u) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) :
    symmetricPower r (orderedSpectralMatrix l u theta q) =
      orderedSpectralMatrix (l ^ r) (u ^ r) theta q := by
  obtain ⟨hp, hm⟩ := orderedSpectralMatrix_spectrum hlu hq
  unfold symmetricPower symmetricDividedPower
  rw [orderedSpectralMatrix_gap hlu hq, hp, hm]
  funext i
  fin_cases i <;>
    simp [orderedSpectralMatrix] <;>
    field_simp [(sub_pos.mpr hlu).ne']

theorem orderedSpectralWeights_inverse {alpha l u : ℝ} (ha : alpha ≠ 0)
    (hl : 0 < l) (hu : 0 < u) :
    orderedSpectralWeights (1 / alpha) (l ^ alpha) (u ^ alpha) =
      fun i => (orderedSpectralWeights alpha l u i)⁻¹ := by
  have hroot {t : ℝ} (ht : 0 < t) : (t ^ alpha) ^ (1 / alpha) = t := by
    rw [← Real.rpow_mul ht.le, show alpha * (1 / alpha) = 1 by field_simp [ha],
      Real.rpow_one]
  have hprod {t : ℝ} (ht : 0 < t) :
      (t ^ alpha) ^ (1 / alpha - 1) * t ^ (alpha - 1) = 1 := by
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht,
      show alpha * (1 / alpha - 1) + (alpha - 1) = 0 by field_simp [ha]; ring,
      Real.rpow_zero]
  have hscalar {t : ℝ} (ht : 0 < t) :
      (1 / alpha) * (t ^ alpha) ^ (1 / alpha - 1) = (alpha * t ^ (alpha - 1))⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (mul_ne_zero ha (Real.rpow_pos_of_pos ht _).ne')).mp
    calc
      _ = ((1 / alpha) * alpha) *
          ((t ^ alpha) ^ (1 / alpha - 1) * t ^ (alpha - 1)) := by ring
      _ = 1 := by rw [hprod ht]; field_simp [ha]
  funext i
  fin_cases i
  · exact hscalar hu
  · exact hscalar hl
  · change ((u ^ alpha) ^ (1 / alpha) - (l ^ alpha) ^ (1 / alpha)) /
      (u ^ alpha - l ^ alpha) = ((u ^ alpha - l ^ alpha) / (u - l))⁻¹
    rw [hroot hu, hroot hl, inv_div]

theorem orderedSpectralWeights_positive {r l u : ℝ} (hr : 0 < r) (hl : 0 < l) (hlu : l < u) :
    ∀ i, 0 < orderedSpectralWeights r l u i := by
  intro i
  fin_cases i
  · exact mul_pos hr (Real.rpow_pos_of_pos (hl.trans hlu) _)
  · exact mul_pos hr (Real.rpow_pos_of_pos hl _)
  · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow hl.le hlu hr)) (sub_pos.mpr hlu)

theorem orderedSpectralWeights_negative {r l u : ℝ} (hr : r < 0) (hl : 0 < l) (hlu : l < u) :
    ∀ i, orderedSpectralWeights r l u i < 0 := by
  intro i
  fin_cases i
  · exact mul_neg_of_neg_of_pos hr (Real.rpow_pos_of_pos (hl.trans hlu) _)
  · exact mul_neg_of_neg_of_pos hr (Real.rpow_pos_of_pos hl _)
  · exact div_neg_of_neg_of_pos (sub_neg.mpr (Real.rpow_lt_rpow_of_neg hl hlu hr))
      (sub_pos.mpr hlu)

theorem symmetricPowerVariation_inverse_cauchy {alpha : ℝ} (ha : alpha ≠ 0)
    (m Z J : Fin 3 → ℝ) (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : m 2 ≠ 0) :
    symmetricTraceProduct Z J ^ 2 ≤
      symmetricTraceProduct J (symmetricPowerVariation (1 / alpha) (symmetricPower alpha m) J) *
        symmetricTraceProduct Z (symmetricPowerVariation alpha m Z) := by
  let l := symmetricMinus m
  let u := symmetricPlus m
  let theta := symmetricTheta m
  let q := symmetricEigenCross m
  have hl : 0 < l := (symmetricEigenvalues_positive hm hdet).1
  have hu : 0 < u := (symmetricEigenvalues_positive hm hdet).2
  have hlu : l < u := by
    change symmetricMinus m < symmetricPlus m
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hq : q ^ 2 = theta * (1 - theta) := symmetricEigenCoordinates_relation m hc
  have hrepr : orderedSpectralMatrix l u theta q = m := symmetricSpectralRepresentation m hc
  have hn : l ^ alpha ≠ u ^ alpha := by
    intro he
    exact (ne_of_lt hlu) ((Real.rpow_left_inj hl.le hu.le ha).mp he)
  rw [← hrepr, orderedSpectralMatrix_power hlu hq,
    unorderedSpectralMatrix_power_variation hn hq, orderedSpectralMatrix_power_variation hlu hq,
    orderedSpectralWeights_inverse ha hl hu]
  rcases lt_or_gt_of_ne ha with ha | ha
  · have h := spectralWeightedMap_negative_cauchy hq (orderedSpectralWeights alpha l u) Z J
      (orderedSpectralWeights_negative ha hl hlu)
    simpa only [mul_comm] using h
  · have h := spectralWeightedMap_cauchy hq (orderedSpectralWeights alpha l u) Z J
      (orderedSpectralWeights_positive ha hl hlu)
    simpa only [mul_comm] using h

theorem symmetricPowerVariation_inverse_spectral {alpha : ℝ} (ha : alpha ≠ 0)
    (m Z : Fin 3 → ℝ) (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : m 2 ≠ 0) :
    symmetricPowerVariation (1 / alpha) (symmetricPower alpha m) Z =
      spectralWeightedMap (symmetricTheta m) (symmetricEigenCross m)
        (fun i => (orderedSpectralWeights alpha (symmetricMinus m) (symmetricPlus m) i)⁻¹) Z := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hu := (symmetricEigenvalues_positive hm hdet).2
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hq := symmetricEigenCoordinates_relation m hc
  have hn : symmetricMinus m ^ alpha ≠ symmetricPlus m ^ alpha := by
    intro he
    exact (ne_of_lt hlu) ((Real.rpow_left_inj hl.le hu.le ha).mp he)
  conv_lhs => rw [← symmetricSpectralRepresentation m hc]
  rw [orderedSpectralMatrix_power hlu hq, unorderedSpectralMatrix_power_variation hn hq,
    orderedSpectralWeights_inverse ha hl hu]

theorem symmetricPowerVariation_inverse_nonnegative {alpha : ℝ} (ha : 0 < alpha)
    (m Z : Fin 3 → ℝ) (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : m 2 ≠ 0) :
    0 ≤ symmetricTraceProduct Z (symmetricPowerVariation (1 / alpha) (symmetricPower alpha m) Z) := by
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hw := orderedSpectralWeights_positive ha (symmetricEigenvalues_positive hm hdet).1 hlu
  rw [symmetricPowerVariation_inverse_spectral ha.ne' m Z hm hdet hc]
  exact spectralWeightedMap_trace_nonnegative (symmetricEigenCoordinates_relation m hc) _ Z
    (fun i => (inv_pos.mpr (hw i)).le)

theorem symmetricPowerVariation_inverse_nonpositive {alpha : ℝ} (ha : alpha < 0)
    (m Z : Fin 3 → ℝ) (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : m 2 ≠ 0) :
    symmetricTraceProduct Z (symmetricPowerVariation (1 / alpha) (symmetricPower alpha m) Z) ≤ 0 := by
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hw := orderedSpectralWeights_negative ha (symmetricEigenvalues_positive hm hdet).1 hlu
  rw [symmetricPowerVariation_inverse_spectral ha.ne m Z hm hdet hc]
  exact spectralWeightedMap_trace_nonpositive (symmetricEigenCoordinates_relation m hc) _ Z
    (fun i => (inv_lt_zero.mpr (hw i)).le)

end

end ResearchMain.DiagonalSchatten
