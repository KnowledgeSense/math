import MainTheorems.DiagonalSchatten.OrderedPowerDuality

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem symmetricPowerVariation_inverse_apply {r : ℝ} (hr : r ≠ 0)
    (m z : Fin 3 → ℝ) (hm : 0 < m 0) (hd : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : m 2 ≠ 0) :
    symmetricPowerVariation (1 / r) (symmetricPower r m) (symmetricPowerVariation r m z) = z := by
  obtain ⟨hl, _⟩ := symmetricEigenvalues_positive hm hd
  have hlu : symmetricMinus m < symmetricPlus m := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hw : ∀ i, orderedSpectralWeights r (symmetricMinus m) (symmetricPlus m) i ≠ 0 := by
    rcases lt_or_gt_of_ne hr with hr | hr
    · exact fun i => (orderedSpectralWeights_negative hr hl hlu i).ne
    · exact fun i => (orderedSpectralWeights_positive hr hl hlu i).ne'
  rw [symmetricPowerVariation_inverse_spectral hr m _ hm hd hc,
    symmetricPowerVariation_spectral r m z hc,
    spectralWeightedMap_inverse (symmetricEigenCoordinates_relation m hc) _ _ hw]

end

end ResearchMain.DiagonalSchatten
