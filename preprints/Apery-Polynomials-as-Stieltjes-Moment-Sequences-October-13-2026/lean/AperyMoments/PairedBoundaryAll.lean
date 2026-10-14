import AperyMoments.PairedExteriorBounds

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem pairedMomentKernel_tendsto_negative {α x : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hx : x<0) (hz : 0<z.im) :
    Tendsto (fun y:ℝ=>pairedMomentKernel α y z x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Tendsto (fun y:ℝ=>y) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hcc := Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  have hp : Tendsto (fun y:ℝ=>(x:ℂ)+y*I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,add_zero] using
      (hcc.mul_const I).const_add (x:ℂ)
  have hM := (momentTransform_analyticAt_negative hα hα1 hx).continuousAt.tendsto.comp hp
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hM
  rw [momentTransform_negative α hx,leftResolvent_real hα hα1 hx] at hi
  have hv := hcc.mul hM
  simp only [Complex.ofReal_zero,zero_mul] at hv
  have hl := pairedCauchyKernel_tendsto (t := fun _:ℝ=>x) hz tendsto_const_nhds hc hi hv
  simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero,zero_div,pairedMomentKernel,pairedCauchyKernel] using hl

theorem pairedMomentKernel_tendsto_ae {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hz : 0<z.im) :
    ∀ᵐ x:ℝ, Tendsto (fun y:ℝ=>pairedMomentKernel α y z x) (𝓝[>] (0:ℝ))
      (𝓝 ((2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ)))) := by
  have he : ∀ᵐ x:ℝ,x∉jumpExceptionalSet α := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using (jumpExceptionalSet_finite α).measure_zero volume
  filter_upwards [he] with x hx
  have hx0 : x≠0 := by intro h; exact hx (Or.inl (by simp [h]))
  rcases lt_or_gt_of_ne hx0 with hn | hp
  · have hd : reciprocalMomentDensity α x=0 := by simp [reciprocalMomentDensity,not_lt.mpr hn.le]
    simpa only [hd,Complex.ofReal_zero,mul_zero,zero_div] using
      pairedMomentKernel_tendsto_negative hα hα1 hn hz
  · exact pairedMomentKernel_tendsto_positive hα hp hx hz tendsto_const_nhds
      nhdsWithin_le_nhds self_mem_nhdsWithin

end AperyMoments
