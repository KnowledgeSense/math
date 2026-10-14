import MainTheorems.DiagonalSchatten.SpectralRay

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem spectralRay_denominator_positive {alpha t theta s : ℝ}
    (ha : 1 < alpha ∨ alpha < -2) (ht : 0 < t) (hs : s ^ 2 = 1)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hc : 0 < spectralCross s t theta / alpha) (Z : Fin 3 → ℝ)
    (x : Fin 2 → ℝ) (hx0 : 0 ≤ x 0) (hx1 : 0 ≤ x 1)
    (hx : 0 < x 0 ∨ 0 < x 1) :
    0 < (spectralRay alpha t theta s Z).denominator x := by
  have hA := spectralFirst_pos ht h0 h1
  have hB := spectralSecond_pos ht h0 h1
  rcases ha with ha | ha
  · have hp : 0 < alpha := by linarith
    have hcp : 0 < spectralCross s t theta := (div_pos_iff_of_pos_right hp).mp hc
    exact (spectralRay alpha t theta s Z).denominator_upper x
      (div_pos (by norm_num) hp) hA hB hcp hx0 hx1 hx
  · have hn : alpha < 0 := by linarith
    have hcn : spectralCross s t theta < 0 := by
      by_contra h
      have hd := div_nonpos_of_nonneg_of_nonpos (not_lt.mp h) hn.le
      linarith
    have hk1 : -1 < 2 / alpha := (lt_div_iff_of_neg hn).mpr (by linarith)
    have hkn : 2 / alpha < 0 := div_neg_of_pos_of_neg (by norm_num) hn
    have hd := spectral_determinant (t := t) hs h0 h1
    exact (spectralRay alpha t theta s Z).denominator_lower x hk1 hkn hA hB hcn
      (by
        change spectralCross s t theta ^ 2 < spectralFirst t theta * spectralSecond t theta
        linarith) hx0 hx1 hx

theorem spectral_two_column_bound {alpha t theta s sign : ℝ}
    (ha : (1 < alpha ∧ sign = 1) ∨ (alpha < -2 ∧ sign = -1))
    (ht : 0 < t) (ht1 : t ≠ 1) (hs : s ^ 2 = 1)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hC : 0 < spectralCross s (t ^ alpha) theta)
    (T : Matrix (Fin 2) (Fin 2) ℝ) (Z : Fin 3 → ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (hA : gramFirst T = spectralFirst (t ^ alpha) theta)
    (hB : gramSecond T = spectralSecond (t ^ alpha) theta)
    (hCT : gramCross T = spectralCross s (t ^ alpha) theta) :
    sign * (∑ j, (spectralRay alpha t theta s Z).functional (fun i => T i j)) ≤
      sign * (symmetricTraceProduct Z (symmetricPowerVariation alpha
        (twoSpectralMatrix t theta (s * Real.sqrt (theta * (1 - theta)))) Z) / 2) := by
  have han : alpha ≠ 0 := by rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have htd : 0 < gramFirst T * gramSecond T - gramCross T ^ 2 := by
    rw [hA, hB, hCT, spectral_determinant hs h0 h1]
    exact Real.rpow_pos_of_pos ht alpha
  have htc : 0 < gramCross T := by rw [hCT]; exact hC
  rcases ha with ⟨ha, rfl⟩ | ⟨ha, rfl⟩
  · have hp : 2 < 2 + 2 / alpha := by
      have hdiv := div_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < alpha)
      linarith
    have h := two_column_ray_nonnegative_upper hp T Z hT htd htc
    rw [compressionRay_spectral han ht ht1 hs h0 h1 T Z hA hB hCT,
      inverseGramQuadratic_spectral han ht ht1 hs h0 h1 T Z hA hB hCT] at h
    simpa using h
  · have hn : alpha < 0 := by linarith
    have hdiv : -1 < 2 / alpha := (lt_div_iff_of_neg hn).mpr (by linarith)
    have hp : 1 < 2 + 2 / alpha := by linarith
    have hp2 : 2 + 2 / alpha < 2 := by
      have hneg := div_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 2) hn
      linarith
    have h := two_column_ray_nonnegative_lower hp hp2 T Z hT htd htc
    rw [compressionRay_spectral han ht ht1 hs h0 h1 T Z hA hB hCT,
      inverseGramQuadratic_spectral han ht ht1 hs h0 h1 T Z hA hB hCT] at h
    simpa only [neg_one_mul, neg_le_neg_iff] using h

end

end ResearchMain.DiagonalSchatten
