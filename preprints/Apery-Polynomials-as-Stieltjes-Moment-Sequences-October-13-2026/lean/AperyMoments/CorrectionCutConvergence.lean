import AperyMoments.CorrectionCutLimits
import AperyMoments.SpectralBoundaryIntegrable

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem correctionWeight_continuousOn : ContinuousOn correctionWeight (Ioo 0 1) := by
  unfold correctionWeight
  apply ContinuousOn.rpow_const (by fun_prop)
  intro v hv
  left
  linarith [hv.2]

theorem correctionWeighted_comp_continuousOn {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w.im < 0)
    {q : ℝ → ℝ} (hq : ContinuousOn q (Ioo 0 1)) (hqi : ∀ v ∈ Ioo 0 1, q v ∈ Ioo 0 1) :
    ContinuousOn (fun v => correctionRegular b w (q v) * (correctionWeight (q v) : ℂ)) (Ioo 0 1) := by
  apply ContinuousOn.mul
  · exact (correctionRegular_continuousOn_interval hb (Or.inl hw)).comp hq
      (fun v hv => ⟨(hqi v hv).1.le, (hqi v hv).2.le⟩)
  · exact Complex.continuous_ofReal.continuousOn.comp (correctionWeight_continuousOn.comp hq hqi)
      (fun _ _ => mem_univ _)

theorem correctionFirstKernel_continuousOn {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w.im < 0)
    (hA : 1 < correctionCutScale b w) : ContinuousOn (correctionFirstKernel b w) (Ioo 0 1) := by
  unfold correctionFirstKernel
  apply (show ContinuousOn (fun _ : ℝ => (correctionCutScale b w)⁻¹) (Ioo 0 1) from continuousOn_const).smul
  exact correctionWeighted_comp_continuousOn hb hw (by fun_prop)
    (fun _ hv => correctionFirstPoint_mem hA hv)

theorem correctionSecondKernel_continuousOn {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w.im < 0)
    (hA : 1 < correctionCutScale b w) : ContinuousOn (correctionSecondKernel b w) (Ioo 0 1) := by
  unfold correctionSecondKernel
  apply (show ContinuousOn (fun _ : ℝ => 1 - (correctionCutScale b w)⁻¹) (Ioo 0 1) from continuousOn_const).smul
  exact correctionWeighted_comp_continuousOn hb hw (by unfold correctionSecondPoint; fun_prop)
    (fun _ hv => correctionSecondPoint_mem hA hv)

/-- Dominated convergence also records integrability of the actual boundary integrand. -/
theorem cut_integral_limit_with_integrability (a : ℝ) (F : ℂ → ℝ → ℂ) (f : ℝ → ℂ) (bound : ℝ → ℝ)
    (hm : ∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] (a : ℂ), AEStronglyMeasurable (F z) (volume.restrict (Ioo 0 1)))
    (hb : ∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] (a : ℂ), ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1), ‖F z v‖ ≤ bound v)
    (hi : IntegrableOn bound (Ioo 0 1))
    (hl : ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1),
      Tendsto (fun z => F z v) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝 (f v))) :
    IntervalIntegrable f volume 0 1 ∧
      Tendsto (fun z => ∫ v in (0 : ℝ)..1, F z v) (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
        (𝓝 (∫ v in (0 : ℝ)..1, f v)) := by
  have hs := lowerVerticalSequence_tendsto a
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually (hm.and hb))
  have hshift : Tendsto (fun n : ℕ => lowerVerticalSequence a (n + N)) atTop
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) := hs.comp (tendsto_add_atTop_nat N)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F (lowerVerticalSequence a (n + N))) (volume.restrict (Ioo 0 1)) :=
    (hN (n + N) (by omega)).1
  have hbound (n : ℕ) : ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1),
      ‖F (lowerVerticalSequence a (n + N)) v‖ ≤ bound v := (hN (n + N) (by omega)).2
  have hlim : ∀ᵐ v : ℝ ∂volume.restrict (Ioo 0 1),
      Tendsto (fun n : ℕ => F (lowerVerticalSequence a (n + N)) v) atTop (𝓝 (f v)) := by
    filter_upwards [hl] with v hv
    exact hv.comp hshift
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact ⟨aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim,
      hasFiniteIntegral_of_dominated_convergence hi.hasFiniteIntegral hbound hlim⟩
  · simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    exact tendsto_integral_filter_of_dominated_convergence bound hm hb hi hl

end AperyMoments
