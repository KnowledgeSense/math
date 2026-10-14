import AperyMoments.CorrectionCutKernels
import AperyMoments.EllipticCutContinuity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem correctionParameter_ofReal (b w v : ℝ) :
    correctionParameter b (w : ℂ) v = ((((w - b) * v / 4) ^ 2 : ℝ) : ℂ) := by
  unfold correctionParameter
  push_cast
  rfl

theorem correctionParameter_composed_boundary {b w : ℝ} (hw : b < w) {u : ℂ → ℝ}
    (hu : ContinuousAt u (w : ℂ)) (hu0 : 0 < u (w : ℂ))
    (hm : ((w - b) * u (w : ℂ) / 4) ^ 2 ≠ 1) :
    Tendsto (fun z : ℂ => complexEllipticK (correctionParameter b z (u z)))
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (complexEllipticK (correctionParameter b (w : ℂ) (u (w : ℂ))))) := by
  have hcont : ContinuousAt (fun z : ℂ => correctionParameter b z (u z)) (w : ℂ) := by
    unfold correctionParameter
    fun_prop
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hdomain : correctionParameter b (w : ℂ) (u (w : ℂ)) ∈ ellipticDomain := by
      right
      rw [correctionParameter_ofReal]
      exact hm
    exact ((complexEllipticK_analyticOnNhd _ hdomain).continuousAt.comp (f := fun z : ℂ => correctionParameter b z (u z)) hcont).tendsto.mono_left nhdsWithin_le_nhds
  · rw [correctionParameter_ofReal]
    apply (complexEllipticK_lower_cut_boundary hm).comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [correctionParameter_ofReal] using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
    · have hr : ∀ᶠ z : ℂ in 𝓝[{z : ℂ | z.im < 0}] (w : ℂ), b < z.re :=
        (Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (Ioi_mem_nhds hw)
      have hv : ∀ᶠ z : ℂ in 𝓝[{z : ℂ | z.im < 0}] (w : ℂ), 0 < u z :=
        (hu.tendsto.mono_left nhdsWithin_le_nhds).eventually (Ioi_mem_nhds hu0)
      filter_upwards [hr, hv, self_mem_nhdsWithin] with z hz hvz him
      exact correctionParameter_im_neg him hz hvz

theorem correctionWeighted_composed_boundary {b w : ℝ} (hb : 0 < b) (hw : b < w) {u : ℂ → ℝ}
    (hu : ContinuousAt u (w : ℂ)) (huI : u (w : ℂ) ∈ Ioo 0 1)
    (hm : ((w - b) * u (w : ℂ) / 4) ^ 2 ≠ 1) :
    Tendsto (fun z : ℂ => correctionRegular b z (u z) * (correctionWeight (u z) : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (correctionRegular b (w : ℂ) (u (w : ℂ)) * (correctionWeight (u (w : ℂ)) : ℂ))) := by
  have hbase := correctionBase_mem_slitPlane_central (w := (w : ℂ)) hb
    (by simpa using (show -b < w by linarith)) ⟨huI.1.le, huI.2.le⟩
  have hbcont : ContinuousAt (fun z : ℂ => correctionBase b z (u z)) (w : ℂ) := by
    unfold correctionBase
    fun_prop
  have hpow := (continuousAt_cpow_const (b := -(1 / 2 : ℂ)) hbase).comp (f := fun z : ℂ => correctionBase b z (u z)) hbcont
  have hwcont : ContinuousAt (fun z : ℂ => (correctionWeight (u z) : ℂ)) (w : ℂ) := by
    apply Complex.continuous_ofReal.continuousAt.comp
    unfold correctionWeight
    exact (continuousAt_const.sub hu).rpow_const (Or.inl (by change 1 - u (w : ℂ) ≠ 0; linarith [huI.2]))
  unfold correctionRegular
  exact ((correctionParameter_composed_boundary hw hu huI.1 hm).mul
    (hpow.tendsto.mono_left nhdsWithin_le_nhds)).mul (hwcont.tendsto.mono_left nhdsWithin_le_nhds)

theorem correctionFirstKernel_boundary {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    Tendsto (fun z : ℂ => correctionFirstKernel b z v)
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ)) (𝓝 (correctionFirstKernel b (w : ℂ) v)) := by
  have hA : 1 < correctionCutScale b (w : ℂ) := by rw [correctionCutScale_ofReal (by linarith)]; linarith
  have hA0 : correctionCutScale b (w : ℂ) ≠ 0 := by linarith
  have hu : ContinuousAt (fun z : ℂ => v / correctionCutScale b z) (w : ℂ) :=
    continuousAt_const.div (correctionCutScale_continuous b).continuousAt hA0
  have hp := correctionFirstPoint_mem hA hv
  have hm : ((w - b) * (v / correctionCutScale b (w : ℂ)) / 4) ^ 2 ≠ 1 := by
    rw [correctionCutScale_ofReal (by linarith)]
    have he : (w - b) * (v / ((w - b) / 4)) / 4 = v := by field_simp [show w - b ≠ 0 by linarith]
    rw [he]
    nlinarith [hv.1, hv.2]
  have h := correctionWeighted_composed_boundary hb (by linarith : b < w) hu hp hm
  have hc := ((correctionCutScale_continuous b).continuousAt.inv₀ hA0).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  exact hc.smul h

theorem correctionSecondKernel_boundary {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    Tendsto (fun z : ℂ => correctionSecondKernel b z v)
      (𝓝[{z : ℂ | z.im < 0}] (w : ℂ)) (𝓝 (correctionSecondKernel b (w : ℂ) v)) := by
  have hA : 1 < correctionCutScale b (w : ℂ) := by rw [correctionCutScale_ofReal (by linarith)]; linarith
  have hA0 : correctionCutScale b (w : ℂ) ≠ 0 := by linarith
  have hu : ContinuousAt (fun z : ℂ => correctionSecondPoint b z v) (w : ℂ) := by
    unfold correctionSecondPoint
    exact (continuousAt_const.add (((correctionCutScale_continuous b).continuousAt.sub continuousAt_const).mul continuousAt_const)).div
      (correctionCutScale_continuous b).continuousAt hA0
  have hp := correctionSecondPoint_mem hA hv
  have hraw : 0 < (((w : ℂ).re - b) ^ 2 - (w : ℂ).im ^ 2) := by simp; nlinarith
  have hm : ((w - b) * correctionSecondPoint b (w : ℂ) v / 4) ^ 2 ≠ 1 := by
    have he := correctionParameter_second_re hraw v
    rw [correctionParameter_ofReal] at he
    change ((w - b) * correctionSecondPoint b (w : ℂ) v / 4) ^ 2 = _ at he
    rw [he]
    have hpv := mul_pos (sub_pos.mpr hA) hv.1
    nlinarith
  have h := correctionWeighted_composed_boundary hb (by linarith : b < w) hu hp hm
  have hc := ((show ContinuousAt (fun _ : ℂ => (1 : ℝ)) (w : ℂ) from continuousAt_const).sub ((correctionCutScale_continuous b).continuousAt.inv₀ hA0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  exact hc.smul h

end AperyMoments
