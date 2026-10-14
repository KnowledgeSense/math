import AperyMoments.CorrectionCutConvergence

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem correctionCut_neighborhood {b w : ℝ} (hw : b + 4 < w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ,
      ∀ᶠ z : ℂ in 𝓝[{z : ℂ | z.im < 0}] (w : ℂ),
        b < z.re ∧ δ ≤ correctionCutScale b z - 1 ∧ correctionCutScale b z ≤ M ∧ z.im < 0 := by
  let A := correctionCutScale b (w : ℂ)
  have hA : 1 < A := by dsimp [A]; rw [correctionCutScale_ofReal (by linarith)]; linarith
  let δ := (A - 1) / 2
  let M := A + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, M, ?_⟩
  have hcont : Tendsto (correctionCutScale b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ)) (𝓝 A) :=
    (correctionCutScale_continuous b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hre : Tendsto (fun z : ℂ => z.re) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ)) (𝓝 w) :=
    Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : 1 + δ < A := by dsimp [δ]; linarith
  have hhigh : A < M := by dsimp [M]; linarith
  filter_upwards [hcont.eventually (Ioo_mem_nhds hlow hhigh),
    hre.eventually (Ioi_mem_nhds (show b < w by linarith)), self_mem_nhdsWithin] with z hz hr hi
  exact ⟨hr, by linarith [hz.1], hz.2.le, hi⟩

theorem correctionFirstIntegral_boundary {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w) :
    IntervalIntegrable (correctionFirstKernel b (w : ℂ)) volume 0 1 ∧
      Tendsto (fun z => ∫ v in (0 : ℝ)..1, correctionFirstKernel b z v)
        (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
        (𝓝 (∫ v in (0 : ℝ)..1, correctionFirstKernel b (w : ℂ) v)) := by
  obtain ⟨δ, hδ, M, hnear⟩ := correctionCut_neighborhood hw
  apply cut_integral_limit_with_integrability w (correctionFirstKernel b)
    (correctionFirstKernel b (w : ℂ)) (fun v => correctionCutFirstBound b δ M * correctionWeight v)
  · filter_upwards [hnear] with z hz
    exact (correctionFirstKernel_continuousOn hb hz.2.2.2 (by linarith [hz.2.1])).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [hnear] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact correctionFirstKernel_bound hb hδ hz.1 hz.2.1 hz.2.2.1 hv
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (IntervalIntegrable.const_mul correctionWeight_integrable _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact correctionFirstKernel_boundary hb hw hv

theorem correctionSecondIntegral_boundary {b w : ℝ} (hb : 0 < b) (hw : b + 4 < w) :
    IntervalIntegrable (correctionSecondKernel b (w : ℂ)) volume 0 1 ∧
      Tendsto (fun z => ∫ v in (0 : ℝ)..1, correctionSecondKernel b z v)
        (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
        (𝓝 (∫ v in (0 : ℝ)..1, correctionSecondKernel b (w : ℂ) v)) := by
  obtain ⟨δ, hδ, M, hnear⟩ := correctionCut_neighborhood hw
  apply cut_integral_limit_with_integrability w (correctionSecondKernel b)
    (correctionSecondKernel b (w : ℂ)) (fun v => correctionCutSecondBound b δ M * correctionCutEndpointWeight v)
  · filter_upwards [hnear] with z hz
    exact (correctionSecondKernel_continuousOn hb hz.2.2.2 (by linarith [hz.2.1])).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [hnear] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact correctionSecondKernel_bound hb hδ hz.2.2.2 hz.1 hz.2.1 hz.2.2.1 hv
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (IntervalIntegrable.const_mul correctionCutEndpointWeight_integrable _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact correctionSecondKernel_boundary hb hw hv

end AperyMoments
