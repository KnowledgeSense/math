import MainTheorems.DiagonalSchatten.SpectralCoordinates

namespace ResearchMain.DiagonalSchatten

noncomputable section

def orderedSpectralMatrix (l u theta q : ℝ) : Fin 3 → ℝ :=
  ![l + (u - l) * theta, l + (u - l) * (1 - theta), (u - l) * q]

theorem orderedSpectralMatrix_gap {l u theta q : ℝ}
    (hlu : l < u) (hq : q ^ 2 = theta * (1 - theta)) :
    symmetricGap (orderedSpectralMatrix l u theta q) = u - l := by
  have he : ((l + (u - l) * theta) - (l + (u - l) * (1 - theta))) ^ 2 +
      4 * ((u - l) * q) ^ 2 = (u - l) ^ 2 := by
    linear_combination 4 * (u - l) ^ 2 * hq
  change Real.sqrt (((l + (u - l) * theta) - (l + (u - l) * (1 - theta))) ^ 2 +
    4 * ((u - l) * q) ^ 2) = u - l
  rw [he, Real.sqrt_sq (sub_pos.mpr hlu).le]

theorem orderedSpectralMatrix_spectrum {l u theta q : ℝ}
    (hlu : l < u) (hq : q ^ 2 = theta * (1 - theta)) :
    symmetricPlus (orderedSpectralMatrix l u theta q) = u ∧
      symmetricMinus (orderedSpectralMatrix l u theta q) = l := by
  unfold symmetricPlus symmetricMinus
  rw [orderedSpectralMatrix_gap hlu hq]
  simp only [orderedSpectralMatrix, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> ring

def orderedSpectralWeights (r l u : ℝ) : Fin 3 → ℝ :=
  ![r * u ^ (r - 1), r * l ^ (r - 1), (u ^ r - l ^ r) / (u - l)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem orderedSpectralMatrix_power_variation {l u theta q : ℝ}
    (hlu : l < u) (hq : q ^ 2 = theta * (1 - theta)) (r : ℝ) (z : Fin 3 → ℝ) :
    symmetricPowerVariation r (orderedSpectralMatrix l u theta q) z =
      spectralWeightedMap theta q (orderedSpectralWeights r l u) z := by
  have hg : u - l ≠ 0 := (sub_pos.mpr hlu).ne'
  obtain ⟨hplus, hminus⟩ := orderedSpectralMatrix_spectrum hlu hq
  unfold symmetricPowerVariation symmetricDividedPowerVariation
    symmetricPlusVariation symmetricMinusVariation symmetricGapVariation
    symmetricDividedPower
  rw [orderedSpectralMatrix_gap hlu hq, hplus, hminus]
  funext i
  fin_cases i <;>
    simp [orderedSpectralMatrix, spectralWeightedMap, fromSpectralCoordinates,
      spectralCoordinates, orderedSpectralWeights, Pi.mul_apply] <;>
    field_simp [hg] <;> ring_nf <;> simp only [hq] <;> ring

end

end ResearchMain.DiagonalSchatten
