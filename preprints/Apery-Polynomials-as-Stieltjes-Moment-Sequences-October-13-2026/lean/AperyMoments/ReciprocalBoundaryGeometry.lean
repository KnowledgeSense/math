import AperyMoments.OuterResolvent

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem reciprocalMap_tendsto_real (α : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (reciprocalMap α) (𝓝 (x : ℂ)) (𝓝 (reciprocalRadius α x : ℂ)) := by
  have hs : (x : ℂ) ∈ Complex.slitPlane := Or.inl hx
  simpa only [reciprocalMap_ofReal α hx.le] using (reciprocalMap_differentiableAt α hs).continuousAt.tendsto

theorem complex_norm_tendsto_positive {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => ‖z‖) (𝓝 (x : ℂ)) (𝓝 x) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using continuous_norm.tendsto (x : ℂ)

theorem reciprocalMap_tendsto_upper {α x : ℝ} (hx : 0 < x) (hαx : α < x) :
    Tendsto (reciprocalMap α) (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝[{w : ℂ | 0 < w.im}] (reciprocalRadius α x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(reciprocalMap_tendsto_real α hx).mono_left nhdsWithin_le_nhds, ?_⟩
  have hn := (complex_norm_tendsto_positive hx).eventually (Ioi_mem_nhds hαx)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with s hs hsn
  exact (reciprocalMap_im_sign hs α).2.2.mpr hsn

theorem reciprocalMap_tendsto_lower {α x : ℝ} (hx : 0 < x) (hxα : x < α) :
    Tendsto (reciprocalMap α) (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝[{w : ℂ | w.im < 0}] (reciprocalRadius α x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(reciprocalMap_tendsto_real α hx).mono_left nhdsWithin_le_nhds, ?_⟩
  have hn := (complex_norm_tendsto_positive hx).eventually (Iio_mem_nhds hxα)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with s hs hsn
  exact (reciprocalMap_im_sign hs α).1.mpr hsn

theorem reciprocalMap_tendsto_nonreal {α x : ℝ} (hx : 0 < x) (hne : x ≠ α) :
    Tendsto (reciprocalMap α) (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝[{w : ℂ | w.im ≠ 0}] (reciprocalRadius α x : ℂ)) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact (reciprocalMap_tendsto_lower hx h).mono_right
      (nhdsWithin_mono _ (fun _ hi => ne_of_lt hi))
  · exact (reciprocalMap_tendsto_upper hx h).mono_right
      (nhdsWithin_mono _ (fun _ hi => ne_of_gt hi))

end AperyMoments
