import AperyMoments.SpectralEndpointBound
import AperyMoments.CorrectionEndpoint
import AperyMoments.SpectralCentralBoundary

noncomputable section
namespace AperyMoments

def auxiliaryEndpointBound (b : ℝ) : ℝ := spectralEndpointBound b +
  correctionEndpointConstant b*(2 : ℝ)^(1/2 : ℝ)/Real.pi^2

theorem auxiliaryEndpointBound_nonneg {b : ℝ} (hb : 0 < b) :
    0 ≤ auxiliaryEndpointBound b := by
  unfold auxiliaryEndpointBound
  exact add_nonneg (spectralEndpointBound_nonneg hb)
    (div_nonneg (mul_nonneg (correctionEndpointConstant_nonneg hb) (by positivity)) (sq_nonneg _))

theorem continuedAuxiliary_endpoint_bound {b : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hw : w.im < 0) (hD : ‖w-(b : ℂ)‖ ≤ b/2) :
    ‖continuedAuxiliary b w‖ ≤ auxiliaryEndpointBound b := by
  have hr := Complex.abs_re_le_norm (w-(b : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have hr' := abs_le.mp (hr.trans hD)
  have hS := continuedSpectral_endpoint_bound hb hb2 hw (by linarith) (by linarith)
  have hC := continuedCorrection_endpoint_bound hb hw (by linarith) (hD.trans (by linarith))
  have hp := Real.rpow_le_rpow (norm_nonneg (w-(b : ℂ))) (hD.trans (by linarith : b/2 ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 1/2)
  have hC' := hC.trans (mul_le_mul_of_nonneg_left hp (correctionEndpointConstant_nonneg hb))
  unfold continuedAuxiliary auxiliaryEndpointBound
  calc
    _ ≤ ‖continuedSpectral b w‖ + ‖Complex.I*continuedCorrection b w/((Real.pi^2 : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ = ‖continuedSpectral b w‖ + ‖continuedCorrection b w‖/Real.pi^2 := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
    _ ≤ _ := add_le_add hS (div_le_div_of_nonneg_right hC' (sq_nonneg _))

end AperyMoments
