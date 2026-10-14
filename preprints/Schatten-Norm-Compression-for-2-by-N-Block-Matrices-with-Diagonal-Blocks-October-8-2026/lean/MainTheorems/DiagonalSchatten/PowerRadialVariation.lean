import MainTheorems.DiagonalSchatten.OrderedPowerDuality

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem spectralCoordinates_orderedSpectralMatrix (l u theta q : ℝ)
    (hq : q ^ 2 = theta * (1 - theta)) :
    spectralCoordinates theta q (orderedSpectralMatrix l u theta q) = ![u, l, 0] := by
  funext i
  fin_cases i <;>
    simp [spectralCoordinates, orderedSpectralMatrix]
  · linear_combination 2 * (u - l) * hq
  · linear_combination -2 * (u - l) * hq
  · ring

theorem orderedSpectralMatrix_radial_variation {l u theta q : ℝ}
    (hl : 0 < l) (hlu : l < u) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) :
    symmetricPowerVariation r (orderedSpectralMatrix l u theta q)
        (orderedSpectralMatrix l u theta q) =
      r • orderedSpectralMatrix (l ^ r) (u ^ r) theta q := by
  have hpow {x : ℝ} (hx : 0 < x) : x ^ (r - 1) * x = x ^ r := by
    calc
      _ = x ^ (r - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ r := by rw [← Real.rpow_add hx]; congr 1; ring
  rw [orderedSpectralMatrix_power_variation hlu hq]
  unfold spectralWeightedMap
  rw [spectralCoordinates_orderedSpectralMatrix _ _ _ _ hq]
  have he : orderedSpectralWeights r l u * (![u, l, 0] : Fin 3 → ℝ) =
      ![r * u ^ r, r * l ^ r, 0] := by
    funext i
    fin_cases i
    · change (r * u ^ (r - 1)) * u = r * u ^ r
      rw [mul_assoc, hpow (hl.trans hlu)]
    · change (r * l ^ (r - 1)) * l = r * l ^ r
      rw [mul_assoc, hpow hl]
    · simp [orderedSpectralWeights]
  rw [he]
  funext i
  fin_cases i <;>
    simp [fromSpectralCoordinates, orderedSpectralMatrix, Pi.smul_apply, smul_eq_mul] <;> ring

theorem symmetricPowerVariation_radial (r : ℝ) (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    symmetricPowerVariation r m m = r • symmetricPower r m := by
  have hl := (symmetricEigenvalues_positive hm hdet).1
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hq := symmetricEigenCoordinates_relation m hc
  rw [← symmetricSpectralRepresentation m hc, orderedSpectralMatrix_radial_variation hl hlu hq,
    orderedSpectralMatrix_power hlu hq]

theorem symmetricPowerVariation_trace_symmetric (r : ℝ) (m z w : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    symmetricTraceProduct z (symmetricPowerVariation r m w) =
      symmetricTraceProduct w (symmetricPowerVariation r m z) := by
  rw [symmetricPowerVariation_spectral r m w hc, symmetricPowerVariation_spectral r m z hc]
  exact spectralWeightedMap_trace_symmetric (symmetricEigenCoordinates_relation m hc) _ z w

theorem symmetricPowerVariation_add (r : ℝ) (m z w : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    symmetricPowerVariation r m (z + w) =
      symmetricPowerVariation r m z + symmetricPowerVariation r m w := by
  simp only [symmetricPowerVariation_spectral r m _ hc]
  exact spectralWeightedMap_add _ _ _ z w

theorem symmetricPowerVariation_smul (r t : ℝ) (m z : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    symmetricPowerVariation r m (t • z) = t • symmetricPowerVariation r m z := by
  simp only [symmetricPowerVariation_spectral r m _ hc]
  exact spectralWeightedMap_smul _ _ t _ z

end

end ResearchMain.DiagonalSchatten
