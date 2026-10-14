import AperyMoments.CorrectionCentral
import AperyMoments.EllipticCut

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def correctionRegularDisk (b : ℝ) : Set ℂ := {w | -b < w.re ∧ ‖w - b‖ < 4}

theorem correctionRegularDisk_isOpen (b : ℝ) : IsOpen (correctionRegularDisk b) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (show Continuous (fun w : ℂ => ‖w - (b : ℂ)‖) by fun_prop) continuous_const)

theorem correctionRegular_continuousOn_disk {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun p : ℂ × ℝ => correctionRegular b p.1 p.2)
      (correctionRegularDisk b ×ˢ Icc 0 1) := by
  unfold correctionRegular
  apply ContinuousOn.mul
  · apply complexEllipticK_continuousOn.comp
    · unfold correctionParameter
      fun_prop
    · intro p hp
      exact correctionParameter_mem_domain_central hp.1.2 hp.2
  · apply ContinuousOn.cpow_const
    · unfold correctionBase
      fun_prop
    · intro p hp
      exact correctionBase_mem_slitPlane_central hb hp.1.1 hp.2

theorem correctionRegular_weighted_continuousAt {b : ℝ} (hb : 0 < b) {w : ℂ}
    (hw : w ∈ correctionRegularDisk b) :
    ContinuousAt (fun z : ℂ => ∫ v in (0 : ℝ)..1,
      correctionRegular b z v * (correctionWeight v : ℂ)) w := by
  have hopen := correctionRegularDisk_isOpen b
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hopen w hw
  have hc : closedBall w (ε / 2) ⊆ correctionRegularDisk b :=
    (closedBall_subset_ball (by linarith)).trans he
  have hcompact := (isCompact_closedBall w (ε / 2)).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    ((correctionRegular_continuousOn_disk hb).mono (fun p hp => ⟨hc hp.1, hp.2⟩))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun v => C * |correctionWeight v|)
  · filter_upwards [hopen.mem_nhds hw] with z hz
    have hcont : ContinuousOn (correctionRegular b z) (Icc 0 1) :=
      (correctionRegular_continuousOn_disk hb).comp (f := fun v : ℝ => (z, v))
        (by fun_prop) (fun v hv => ⟨hz, hv⟩)
    have hi : IntervalIntegrable (fun v => (correctionWeight v : ℂ)) volume 0 1 :=
      ⟨correctionWeight_integrable.1.ofReal, correctionWeight_integrable.2.ofReal⟩
    have hprod := IntervalIntegrable.continuousOn_mul hi
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont)
    exact hprod.def'.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds w (by linarith : 0 < ε / 2)] with z hz
    apply Eventually.of_forall
    intro v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact hC (z, v) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le, hv.1.le, hv.2⟩
  · exact IntervalIntegrable.const_mul correctionWeight_integrable.abs C
  · apply Eventually.of_forall
    intro v hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have hcont : ContinuousOn (fun z : ℂ => correctionRegular b z v) (correctionRegularDisk b) :=
      (correctionRegular_continuousOn_disk hb).comp (f := fun z : ℂ => (z, v))
        (by fun_prop) (fun z hz => ⟨hz, hv.1.le, hv.2⟩)
    exact (hcont.continuousAt (hopen.mem_nhds hw)).tendsto.mul_const _

/-- Before the second elliptic cut, the oriented correction has its actual principal value
as its unrestricted lower boundary. -/
theorem continuedCorrection_right_boundary_before_cut {b w : ℝ} (hb : 0 < b)
    (hw : b < w) (hw4 : w < b + 4) :
    Tendsto (continuedCorrection b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (continuedCorrection b (w : ℂ))) := by
  have hdisk : (w : ℂ) ∈ correctionRegularDisk b := by
    constructor
    · simpa using (show -b < w by linarith)
    · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hw)]
      linarith
  have hbase : Tendsto (fun z : ℂ => (b : ℂ) - z)
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((b - w : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_sub] using
        (show ContinuousAt (fun z : ℂ => (b : ℂ) - z) (w : ℂ) by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using (neg_pos.mpr hz).le
  have hp := (cpow_continuousWithinAt_upper_real (by linarith : b - w ≠ 0) (-(1 / 2 : ℂ))).tendsto.comp hbase
  have hi := (correctionRegular_weighted_continuousAt hb hdisk).tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  have hbse := (show ContinuousAt (fun z : ℂ => (b : ℂ) - z) (w : ℂ) by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  have h := ((hbse.mul hp).div_const (Real.pi : ℂ)).mul hi
  unfold continuedCorrection
  simpa only [Complex.ofReal_sub, Function.comp_def] using h

end AperyMoments
