import MainTheorems.DiagonalSchatten.PowerRadialVariation

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem orderedSpectralMatrix_scale (l u theta q c : ℝ) :
    orderedSpectralMatrix (c * l) (c * u) theta q =
      c • orderedSpectralMatrix l u theta q := by
  funext i
  fin_cases i <;> simp [orderedSpectralMatrix, Pi.smul_apply, smul_eq_mul] <;> ring

theorem spectralWeightedMap_weights_smul (theta q c : ℝ) (weights z : Fin 3 → ℝ) :
    spectralWeightedMap theta q (c • weights) z = c • spectralWeightedMap theta q weights z := by
  funext i
  fin_cases i <;> simp [spectralWeightedMap, fromSpectralCoordinates,
    Pi.smul_apply, smul_eq_mul, Pi.mul_apply] <;> ring

theorem orderedSpectralWeights_scale {c l u : ℝ}
    (hc : 0 < c) (hl : 0 < l) (hu : 0 < u) (hlu : l ≠ u) (r : ℝ) :
    orderedSpectralWeights r (c * l) (c * u) = c ^ (r - 1) • orderedSpectralWeights r l u := by
  have hp : c ^ r = c * c ^ (r - 1) := by
    rw [Real.rpow_sub hc r 1, Real.rpow_one]
    field_simp [hc.ne']
  funext i
  fin_cases i <;> simp [orderedSpectralWeights, Pi.smul_apply, smul_eq_mul,
    Real.mul_rpow hc.le hl.le, Real.mul_rpow hc.le hu.le]
  · ring
  · ring
  · rw [hp]
    field_simp [hc.ne', sub_ne_zero.mpr (Ne.symm hlu)]

theorem symmetricPower_scale {c : ℝ} (hc : 0 < c) (r : ℝ) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hd : 0 < m 0 * m 1 - m 2 ^ 2) (hcross : m 2 ≠ 0) :
    symmetricPower r (c • m) = c ^ r • symmetricPower r m := by
  obtain ⟨hl, hu⟩ := symmetricEigenvalues_positive hm hd
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hcross
  have hq := symmetricEigenCoordinates_relation m hcross
  have hrep := symmetricSpectralRepresentation m hcross
  conv_lhs => rw [← hrep, ← orderedSpectralMatrix_scale]
  conv_rhs => rw [← hrep]
  rw [orderedSpectralMatrix_power (mul_lt_mul_of_pos_left hlu hc) hq,
    orderedSpectralMatrix_power hlu hq, Real.mul_rpow hc.le hl.le,
    Real.mul_rpow hc.le hu.le, orderedSpectralMatrix_scale]

theorem symmetricPowerVariation_scale {c : ℝ} (hc : 0 < c) (r : ℝ)
    (m z : Fin 3 → ℝ) (hm : 0 < m 0) (hd : 0 < m 0 * m 1 - m 2 ^ 2)
    (hcross : m 2 ≠ 0) :
    symmetricPowerVariation r (c • m) z = c ^ (r - 1) • symmetricPowerVariation r m z := by
  obtain ⟨hl, hu⟩ := symmetricEigenvalues_positive hm hd
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hcross
  have hq := symmetricEigenCoordinates_relation m hcross
  have hrep := symmetricSpectralRepresentation m hcross
  conv_lhs => rw [← hrep, ← orderedSpectralMatrix_scale]
  conv_rhs => rw [← hrep]
  rw [orderedSpectralMatrix_power_variation (mul_lt_mul_of_pos_left hlu hc) hq,
    orderedSpectralMatrix_power_variation hlu hq,
    orderedSpectralWeights_scale hc hl hu (ne_of_lt hlu), spectralWeightedMap_weights_smul]

theorem symmetricTraceProduct_smul_right (Z W : Fin 3 → ℝ) (c : ℝ) :
    symmetricTraceProduct Z (c • W) = c * symmetricTraceProduct Z W := by
  unfold symmetricTraceProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end

end ResearchMain.DiagonalSchatten
