import MainTheorems.DiagonalSchatten.SymmetricPowerScale
import MainTheorems.DiagonalSchatten.SpectralRay

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem positive_spectral_normalization (m : Fin 3 → ℝ)
    (hm : 0 < m 0) (hd : 0 < m 0 * m 1 - m 2 ^ 2) (hc : m 2 ≠ 0) :
    ∃ u t theta s : ℝ, 0 < u ∧ 0 < t ∧ t < 1 ∧ 0 < theta ∧ theta < 1 ∧
      s ^ 2 = 1 ∧ m = u • twoSpectralMatrix t theta
        (s * Real.sqrt (theta * (1 - theta))) := by
  let u := symmetricPlus m
  let l := symmetricMinus m
  let theta := symmetricTheta m
  let q := symmetricEigenCross m
  let t := l / u
  let s := q / Real.sqrt (theta * (1 - theta))
  obtain ⟨hl, hu⟩ := symmetricEigenvalues_positive hm hd
  obtain ⟨htheta, htheta1⟩ := symmetricEigenCoordinates_bounds m hc
  have hlu : l < u := by
    rw [← sub_pos, symmetricEigenvalues_gap]
    exact symmetricGap_positive m hc
  have hq : q ^ 2 = theta * (1 - theta) := symmetricEigenCoordinates_relation m hc
  have hsqrt : 0 < Real.sqrt (theta * (1 - theta)) :=
    Real.sqrt_pos.mpr (mul_pos htheta (sub_pos.mpr htheta1))
  have hsquare := Real.sq_sqrt (mul_nonneg htheta.le (sub_nonneg.mpr htheta1.le))
  have hs : s ^ 2 = 1 := by
    dsimp only [s]
    rw [div_pow, hq, hsquare, div_self (mul_pos htheta (sub_pos.mpr htheta1)).ne']
  have hsq : s * Real.sqrt (theta * (1 - theta)) = q := by
    dsimp only [s]
    exact div_mul_cancel₀ _ hsqrt.ne'
  refine ⟨u, t, theta, s, hu, div_pos hl hu, (div_lt_one hu).mpr hlu,
    htheta, htheta1, hs, ?_⟩
  rw [hsq]
  have hscaled : orderedSpectralMatrix l u theta q = u • twoSpectralMatrix t theta q := by
    rw [twoSpectralMatrix, ← orderedSpectralMatrix_scale]
    have hcancel : u * t = l := by
      dsimp only [t]
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ l (show u ≠ 0 from hu.ne')
    rw [hcancel, mul_one]
  rw [← hscaled]
  exact (symmetricSpectralRepresentation m hc).symm

end

end ResearchMain.DiagonalSchatten
