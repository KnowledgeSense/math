import AperyMoments.CorrectionEndpoint
import AperyMoments.CorrectionUniformBound
import AperyMoments.AuxiliaryOuterBoundary
import AperyMoments.SpectralBoundaryIntegrable

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

def correctionCompactBound (b R : ℝ) : ℝ :=
  correctionEndpointConstant b * (2 : ℝ) ^ (1/2 : ℝ) + ((R+1)/Real.pi)*correctionWeakBound b

theorem correctionCompactBound_nonneg {b R : ℝ} (hb : 0 < b) (hR : 0 ≤ R) :
    0 ≤ correctionCompactBound b R := by
  have he := correctionEndpointConstant_nonneg hb
  have hw := correctionWeakBound_nonneg hb
  unfold correctionCompactBound
  positivity

theorem continuedCorrection_compact_bound {b R w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b+4) (hR : w-b ≤ R) :
    ‖continuedCorrection b (w : ℂ)‖ ≤ correctionCompactBound b R := by
  have hRp : 0 ≤ R := by linarith
  have hc := (continuedCorrection_right_boundary hb hw hne).comp (lowerVerticalSequence_tendsto w)
  have hcn := continuous_norm.continuousAt.tendsto.comp hc
  simp only [Function.comp_def] at hcn
  apply le_of_tendsto hcn
  by_cases hd : w-b < 2
  · have hdlim : Tendsto (fun n => ‖lowerVerticalSequence w n - (b : ℂ)‖) atTop (𝓝 (w-b)) := by
      have ht := (show Continuous (fun z : ℂ => ‖z-(b : ℂ)‖) by fun_prop).continuousAt.tendsto.comp
        ((lowerVerticalSequence_tendsto w).mono_right nhdsWithin_le_nhds)
      simpa only [Function.comp_def, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hw)] using ht
    filter_upwards [hdlim.eventually (Iio_mem_nhds hd)] with n hn
    have he := continuedCorrection_endpoint_bound hb (lowerVerticalSequence_im w n)
      (by rw [lowerVerticalSequence_re]; linarith) (le_of_lt hn)
    have hp := Real.rpow_le_rpow (norm_nonneg (lowerVerticalSequence w n-(b : ℂ))) (le_of_lt hn)
      (by norm_num : (0 : ℝ) ≤ 1/2)
    have hh := mul_le_mul_of_nonneg_left hp (correctionEndpointConstant_nonneg hb)
    have hnon : 0 ≤ ((R+1)/Real.pi)*correctionWeakBound b :=
      mul_nonneg (div_nonneg (by linarith) Real.pi_pos.le) (correctionWeakBound_nonneg hb)
    unfold correctionCompactBound
    linarith
  · apply Eventually.of_forall
    intro n
    have hlow : 2 ≤ ‖lowerVerticalSequence w n-(b : ℂ)‖ := by
      have ht := Complex.re_le_norm (lowerVerticalSequence w n-(b : ℂ))
      simp only [Complex.sub_re, lowerVerticalSequence_re, Complex.ofReal_re] at ht
      linarith
    have hn : (1 : ℝ)/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hhigh : ‖lowerVerticalSequence w n-(b : ℂ)‖ ≤ R+1 := by
      have he : lowerVerticalSequence w n-(b : ℂ) = ((w-b : ℝ) : ℂ) -
          Complex.I * ((1/((n : ℝ)+1) : ℝ) : ℂ) := by unfold lowerVerticalSequence; push_cast; ring
      rw [he]
      apply (norm_sub_le _ _).trans
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hw), norm_mul,
        Complex.norm_I, one_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ)/((n : ℝ)+1))]
      linarith
    have he := continuedCorrection_uniform_bound hb (lowerVerticalSequence_im w n)
      (by rw [lowerVerticalSequence_re]; linarith) hlow hhigh
    have hnon : 0 ≤ correctionEndpointConstant b * (2 : ℝ) ^ (1/2 : ℝ) :=
      mul_nonneg (correctionEndpointConstant_nonneg hb) (by positivity)
    unfold correctionCompactBound
    linarith

theorem continuationCorrection_compact_bound {b R w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b+4) (hR : w-b ≤ R) :
    continuationCorrection b w ≤ correctionCompactBound b R / Real.pi^2 := by
  have hn := continuedCorrection_compact_bound hb hw hne hR
  rw [continuedCorrection_right_complex_value hb hw] at hn
  simp only [norm_mul, Complex.norm_I, one_mul] at hn
  have hr := Complex.re_le_norm (rightCorrectionComplex b w)
  rw [rightCorrectionComplex_re hb hw hne] at hr
  apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith

end AperyMoments
