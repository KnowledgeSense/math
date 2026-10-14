import AperyMoments.CorrectionDecay
import AperyMoments.SpectralDecay
import AperyMoments.SpectralCentralBoundary

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def auxiliaryDecayConstant (b : ℝ) : ℝ :=
  spectralDecayConstant + correctionDecayConstant b * (2 : ℝ) ^ (3 / 8 : ℝ) / Real.pi ^ 2

theorem auxiliaryDecayConstant_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ auxiliaryDecayConstant b := by
  unfold auxiliaryDecayConstant
  have hS := spectralDecayConstant_nonneg
  have hC := correctionDecayConstant_nonneg hb
  positivity

/-- Uniform decay on the entire right lower quadrant; this power bound is sufficient for
Cauchy reconstruction and does not assume an elliptic logarithmic expansion. -/
theorem continuedAuxiliary_decay {b : ℝ} {w : ℂ} (hb : 0 < b)
    (him : w.im < 0) (hre : 0 ≤ w.re) (hn : 4 * b + 32 ≤ ‖w‖) :
    ‖continuedAuxiliary b w‖ ≤ auxiliaryDecayConstant b * ‖w‖ ^ (-(3 / 8 : ℝ)) := by
  have hw0 : 0 < ‖w‖ := by linarith
  have hdist : ‖w‖ - b ≤ ‖w - b‖ := by
    have h := norm_sub_norm_le w (b : ℂ)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] using h
  have hD : 16 ≤ ‖w - b‖ := by linarith
  have hhalf : ‖w‖ / 2 ≤ ‖w - b‖ := by linarith
  have hS := continuedSpectral_decay hb him hre (by linarith : 4 * b ≤ ‖w‖)
  have hC := continuedCorrection_decay hb him hre hD
  have hpS : ‖w‖ ^ (-(7 / 8 : ℝ)) ≤ ‖w‖ ^ (-(3 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hpC := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ‖w‖ / 2) hhalf
    (by norm_num : -(3 / 8 : ℝ) ≤ 0)
  have he : (‖w‖ / 2) ^ (-(3 / 8 : ℝ)) = (2 : ℝ) ^ (3 / 8 : ℝ) * ‖w‖ ^ (-(3 / 8 : ℝ)) := by
    rw [show ‖w‖ / 2 = (2 : ℝ)⁻¹ * ‖w‖ by ring,
      Real.mul_rpow (by norm_num) hw0.le, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he] at hpC
  have hs := mul_le_mul_of_nonneg_left hpS spectralDecayConstant_nonneg
  have hc := mul_le_mul_of_nonneg_left hpC (correctionDecayConstant_nonneg hb)
  have hnorm : ‖Complex.I * continuedCorrection b w / ((Real.pi ^ 2 : ℝ) : ℂ)‖ =
      ‖continuedCorrection b w‖ / Real.pi ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  unfold continuedAuxiliary
  calc
    _ ≤ ‖continuedSpectral b w‖ + ‖Complex.I * continuedCorrection b w / ((Real.pi ^ 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = ‖continuedSpectral b w‖ + ‖continuedCorrection b w‖ / Real.pi ^ 2 := by rw [hnorm]
    _ ≤ spectralDecayConstant * ‖w‖ ^ (-(3 / 8 : ℝ)) +
        (correctionDecayConstant b * ((2 : ℝ) ^ (3 / 8 : ℝ) * ‖w‖ ^ (-(3 / 8 : ℝ)))) / Real.pi ^ 2 := by
      apply add_le_add (hS.trans hs)
      exact div_le_div_of_nonneg_right (hC.trans hc) (sq_nonneg _)
    _ = _ := by unfold auxiliaryDecayConstant; ring

end AperyMoments
