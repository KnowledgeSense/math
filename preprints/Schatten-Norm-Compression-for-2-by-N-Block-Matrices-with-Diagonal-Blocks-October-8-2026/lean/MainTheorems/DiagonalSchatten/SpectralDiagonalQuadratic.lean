import MainTheorems.DiagonalSchatten.TwoSpectralDifferential
import MainTheorems.DiagonalSchatten.SpectralResidual

namespace ResearchMain.DiagonalSchatten

noncomputable section

set_option maxHeartbeats 1000000 in
theorem spectral_diagonal_quadratic {alpha t theta q : ℝ} (ht1 : t ≠ 1)
    (hq : q ^ 2 = theta * (1 - theta)) (x y : ℝ) :
    symmetricTraceProduct ![x, y, 0]
        (symmetricPowerVariation alpha (twoSpectralMatrix t theta q) ![x, y, 0]) / 2 =
      ((alpha * theta ^ 2 + alpha * t ^ (alpha - 1) * (1 - theta) ^ 2 +
        2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2) * x ^ 2 +
      2 * (theta * (1 - theta) *
        (alpha * (1 + t ^ (alpha - 1)) - 2 * ((1 - t ^ alpha) / (1 - t))) / 2) * x * y +
      ((alpha * (1 - theta) ^ 2 + alpha * t ^ (alpha - 1) * theta ^ 2 +
        2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2) * y ^ 2 := by
  rw [twoSpectralMatrix_power_variation ht1 hq, spectralWeightedMap_trace hq]
  simp [twoSpectralWeights, spectralCoordinates]
  field_simp [sub_ne_zero.mpr (Ne.symm ht1)]
  ring_nf
  simp only [hq]
  ring

end

end ResearchMain.DiagonalSchatten
