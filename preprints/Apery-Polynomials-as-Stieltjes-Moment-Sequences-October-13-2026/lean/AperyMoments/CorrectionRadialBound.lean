import AperyMoments.EllipticRadialBound
import AperyMoments.CorrectionKernel
import AperyMoments.ShiftedPowerIntegral

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem correctionParameter_norm (b : ℝ) (w : ℂ) {v : ℝ} (hv : 0 ≤ v) :
    ‖correctionParameter b w v‖ = (‖w - b‖ * v / 4) ^ 2 := by
  unfold correctionParameter
  simp only [norm_pow, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hv]
  norm_num

theorem one_sub_square_abs_bound {t : ℝ} (ht : 0 ≤ t) :
    |1 - t| ≤ |1 - t ^ 2| := by
  rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
  nlinarith [abs_nonneg (1 - t)]

theorem correctionElliptic_radial_bound {b : ℝ} {w : ℂ} {v : ℝ}
    (hz : correctionParameter b w v ∈ ellipticDomain) (hD : 2 ≤ ‖w - b‖)
    (hv : 0 ≤ v) (hne : v ≠ (‖w - b‖ / 4)⁻¹) :
    ‖complexEllipticK (correctionParameter b w v)‖ ≤
      (8 * (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ))) * ‖v - (‖w - b‖ / 4)⁻¹‖ ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
  let A : ℝ := ‖w - b‖ / 4
  have hA : 0 < A := by dsimp [A]; positivity
  have he : 1 - A * v = -A * (v - A⁻¹) := by field_simp; ring
  have hn : 1 - A * v ≠ 0 := by rw [he]; exact mul_ne_zero (neg_ne_zero.mpr hA.ne') (sub_ne_zero.mpr hne)
  have hnorm : ‖correctionParameter b w v‖ = (A * v) ^ 2 := by rw [correctionParameter_norm b w hv]; dsimp [A]; ring
  have hs : ‖correctionParameter b w v‖ ≠ 1 := by
    rw [hnorm]
    intro h
    have hAv : 0 ≤ A * v := mul_nonneg hA.le hv
    have : A * v = 1 := by nlinarith
    exact hn (by linarith)
  have h := complexEllipticK_radial_mild_bound hz hs
  rw [hnorm] at h
  have hp := Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hn)
    (one_sub_square_abs_bound (mul_nonneg hA.le hv)) (by norm_num : -(1 / 16 : ℝ) ≤ 0)
  have hf : |1 - A * v| ^ (-(1 / 16 : ℝ)) = A ^ (-(1 / 16 : ℝ)) * ‖v - A⁻¹‖ ^ (-(1 / 16 : ℝ)) := by
    rw [he, abs_mul, abs_neg, abs_of_pos hA, Real.mul_rpow hA.le (abs_nonneg _), Real.norm_eq_abs]
  have hscale : A ^ (-(1 / 16 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(1 / 16 : ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (by norm_num)
    · dsimp [A]; linarith
    · norm_num
  rw [hf] at hp
  have hm := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg (norm_nonneg (v - A⁻¹)) (-(1 / 16 : ℝ)))
  dsimp only [A] at h hp hm
  nlinarith

end AperyMoments
