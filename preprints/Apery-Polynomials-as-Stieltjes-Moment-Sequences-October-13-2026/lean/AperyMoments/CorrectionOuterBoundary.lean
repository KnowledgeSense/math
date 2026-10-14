import AperyMoments.CorrectionCutSplit

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem correctionRegular_weight_integrable_after_cut {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w) :
    IntervalIntegrable (fun v => correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ)) volume 0 1 := by
  have hA : 1 < correctionCutScale b (w : ℂ) := by
    rw [correctionCutScale_ofReal (by linarith)]
    linarith
  exact correctionCut_integrable_of_halves hA (correctionFirstIntegral_boundary hb hw).1
    (correctionSecondIntegral_boundary hb hw).1

theorem correctionRegular_weighted_boundary_after_cut {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w) :
    Tendsto (fun z : ℂ => ∫ v in (0 : ℝ)..1, correctionRegular b z v * (correctionWeight v : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (∫ v in (0 : ℝ)..1, correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ))) := by
  have hA : 1 < correctionCutScale b (w : ℂ) := by
    rw [correctionCutScale_ofReal (by linarith)]
    linarith
  have h := (correctionFirstIntegral_boundary hb hw).2.add (correctionSecondIntegral_boundary hb hw).2
  rw [← correctionCut_integral_split hA (correctionRegular_weight_integrable_after_cut hb hw)] at h
  apply h.congr'
  obtain ⟨δ, hδ, M, hnear⟩ := correctionCut_neighborhood hw
  filter_upwards [hnear] with z hz
  exact (correctionCut_integral_split (by linarith [hz.2.1])
    (correctionRegular_weight_integrable hb (Or.inl hz.2.2.2))).symm

theorem correctionPrefactor_right_boundary {b w : ℝ} (hw : b < w) :
    Tendsto (fun z : ℂ => ((b : ℂ) - z) * (((b : ℂ) - z) ^ (-(1 / 2 : ℂ))) / (Real.pi : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (((b : ℂ) - (w : ℂ)) * (((b : ℂ) - (w : ℂ)) ^ (-(1 / 2 : ℂ))) / (Real.pi : ℂ))) := by
  have hbase : Tendsto (fun z : ℂ => (b : ℂ) - z)
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((b - w : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_sub] using
        (show ContinuousAt (fun z : ℂ => (b : ℂ) - z) (w : ℂ) by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using (neg_pos.mpr hz).le
  have hp := (cpow_continuousWithinAt_upper_real (by linarith : b - w ≠ 0) (-(1 / 2 : ℂ))).tendsto.comp hbase
  have hbse := (show ContinuousAt (fun z : ℂ => (b : ℂ) - z) (w : ℂ) by fun_prop).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  simpa only [Complex.ofReal_sub, Function.comp_def] using (hbse.mul hp).div_const (Real.pi : ℂ)

theorem continuedCorrection_right_boundary_after_cut {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w) :
    Tendsto (continuedCorrection b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (continuedCorrection b (w : ℂ))) := by
  unfold continuedCorrection
  exact (correctionPrefactor_right_boundary (by linarith : b < w)).mul
    (correctionRegular_weighted_boundary_after_cut hb hw)

/-- The actual oriented correction has its unrestricted lower boundary at every ordinary
positive-axis point; the single coalescing endpoint is treated separately. -/
theorem continuedCorrection_right_boundary {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b + 4) :
    Tendsto (continuedCorrection b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (continuedCorrection b (w : ℂ))) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact continuedCorrection_right_boundary_before_cut hb hw h
  · exact continuedCorrection_right_boundary_after_cut hb h

end AperyMoments
