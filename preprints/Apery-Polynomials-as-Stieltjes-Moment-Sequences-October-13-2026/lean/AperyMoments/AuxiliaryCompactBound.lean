import AperyMoments.AuxiliaryEndpointBound
import AperyMoments.CorrectionUniformBound

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def spectralRightBound (b : ℝ) : ℝ := max (spectralEndpointBound b)
  (latticeWeakConstant*b^(-(1/8 : ℝ))+latticeHalfStripConstant)

theorem spectralRightBound_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ spectralRightBound b :=
  (spectralEndpointBound_nonneg hb).trans (le_max_left _ _)

theorem continuedSpectral_right_bound {b : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hw : w.im < 0) (hre : b/2 ≤ w.re) : ‖continuedSpectral b w‖ ≤ spectralRightBound b := by
  by_cases hu : w.re ≤ 2*b
  · exact (continuedSpectral_endpoint_bound hb hb2 hw hre hu).trans (le_max_left _ _)
  · have hpoint (θ : ℝ) : ‖continuedLattice (w-(b*Real.cos θ : ℝ))‖ ≤
        latticeWeakConstant*b^(-(1/8 : ℝ))+latticeHalfStripConstant := by
      have hr : b ≤ (w-(b*Real.cos θ : ℝ)).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb.le]
      have hp : 0 < (w-(b*Real.cos θ : ℝ)).re := hb.trans_le hr
      have hh := continuedLattice_halfStrip_bound (z := w-(b*Real.cos θ : ℝ))
        (by simpa using hw) (by linarith) hp.ne'
      rw [abs_of_pos hp] at hh
      have ht := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb hr (by norm_num : -(1/8 : ℝ) ≤ 0)) latticeWeakConstant_nonneg
      linarith
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.pi)
      (f := fun θ : ℝ => continuedLattice (w-(b*Real.cos θ : ℝ))) (fun θ _ => hpoint θ)
    simp only [sub_zero, abs_of_pos Real.pi_pos] at hI
    unfold continuedSpectral
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply le_trans _ (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr Real.pi_pos.le)
    simpa only [mul_comm _ Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, mul_inv_cancel₀ Real.pi_ne_zero, one_mul] using hh

def correctionRightBound (b R : ℝ) : ℝ := max
  (correctionEndpointConstant b*(2 : ℝ)^(1/2 : ℝ))
  (((R+b)/Real.pi)*correctionWeakBound b)

theorem correctionRightBound_nonneg {b R : ℝ} (hb : 0 < b) : 0 ≤ correctionRightBound b R :=
  (mul_nonneg (correctionEndpointConstant_nonneg hb) (by positivity)).trans (le_max_left _ _)

theorem continuedCorrection_right_bound {b R : ℝ} {w : ℂ} (hb : 0 < b)
    (hw : w.im < 0) (hre : 0 ≤ w.re) (hn : ‖w‖ ≤ R) :
    ‖continuedCorrection b w‖ ≤ correctionRightBound b R := by
  by_cases hD : ‖w-(b : ℂ)‖ ≤ 2
  · have h := continuedCorrection_endpoint_bound hb hw hre hD
    have hp := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hD (by norm_num : (0 : ℝ) ≤ 1/2))
      (correctionEndpointConstant_nonneg hb)
    exact (h.trans hp).trans (le_max_left _ _)
  · have hM : ‖w-(b : ℂ)‖ ≤ R+b := by
      have h := norm_sub_le w (b : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at h
      linarith
    exact (continuedCorrection_uniform_bound hb hw hre (le_of_not_ge hD) hM).trans (le_max_right _ _)

def auxiliaryRightBound (b R : ℝ) : ℝ := spectralRightBound b+correctionRightBound b R/Real.pi^2

theorem auxiliaryRightBound_nonneg {b R : ℝ} (hb : 0 < b) : 0 ≤ auxiliaryRightBound b R :=
  add_nonneg (spectralRightBound_nonneg hb) (div_nonneg (correctionRightBound_nonneg hb) (sq_nonneg _))

theorem continuedAuxiliary_right_bound {b R : ℝ} {w : ℂ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hw : w.im < 0) (hre : b/2 ≤ w.re) (hn : ‖w‖ ≤ R) :
    ‖continuedAuxiliary b w‖ ≤ auxiliaryRightBound b R := by
  have hS := continuedSpectral_right_bound hb hb2 hw hre
  have hC := continuedCorrection_right_bound hb hw (by linarith) hn
  unfold continuedAuxiliary auxiliaryRightBound
  calc
    _ ≤ ‖continuedSpectral b w‖+‖Complex.I*continuedCorrection b w/((Real.pi^2 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = ‖continuedSpectral b w‖+‖continuedCorrection b w‖/Real.pi^2 := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
    _ ≤ _ := add_le_add hS (div_le_div_of_nonneg_right hC (sq_nonneg _))

end AperyMoments
