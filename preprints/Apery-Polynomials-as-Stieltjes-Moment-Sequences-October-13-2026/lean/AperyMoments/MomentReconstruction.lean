import AperyMoments.PairedExteriorDomination
import AperyMoments.PairedBoundaryAll
import AperyMoments.JumpDensityIntegrable

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem reciprocalMomentKernel_integrable {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hz : z.im≠0) :
    Integrable (densityCauchyKernel (reciprocalMomentDensity α) z) := by
  apply densityCauchyKernel_integrable (reciprocalMomentDensity_measurable α)
    (reciprocalMomentDensity_integrable hα hα1) (abs_pos.mpr hz)
  intro t _
  simpa using Complex.abs_im_le_norm (z-(t:ℂ))

theorem pairedMomentKernel_integral_tendsto {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hz : 0<z.im) :
    Tendsto (fun y:ℝ=>∫ x:ℝ,pairedMomentKernel α y z x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x:ℝ,(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ)))) := by
  obtain ⟨δ,R,hδ,hR,_,B,hBI,_,hbound⟩ := exteriorPairedKernel_dominated hα hα1 hz
  have hsmall : ∀ᶠ y:ℝ in 𝓝[>] (0:ℝ), 0<y ∧ y<z.im := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hz)] with y hy hyz
    exact ⟨hy,hyz⟩
  have hout : Tendsto (fun y=>∫ x:ℝ,exteriorPairedKernel α δ R z y x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x:ℝ,(Icc δ R)ᶜ.indicator
        (fun x=>(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ))) x)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · filter_upwards [hsmall] with y hy
      exact ((pairedMomentKernel_integrable hα hα1 hy.1 hy.2).indicator
        (s := (Icc δ R)ᶜ) measurableSet_Icc.compl).aestronglyMeasurable
    · exact hbound
    · exact hBI
    · filter_upwards [pairedMomentKernel_tendsto_ae hα hα1 hz] with x hx
      by_cases he : x∈(Icc δ R)ᶜ
      · simpa only [exteriorPairedKernel,indicator_of_mem he] using hx
      · simp only [exteriorPairedKernel,indicator_of_notMem he]
        exact tendsto_const_nhds
  simp only [exteriorPairedKernel,integral_indicator measurableSet_Icc.compl] at hout
  have hin := pairedMomentKernel_integral_Icc_tendsto hα hα1 hδ hR hz
  have hsum := hin.add hout
  have hKI : Integrable (fun x:ℝ=>(2*Real.pi*I)*(reciprocalMomentDensity α x:ℂ)/(z-(x:ℂ))) := by
    simpa only [densityCauchyKernel,mul_div_assoc] using
      (reciprocalMomentKernel_integrable hα hα1 hz.ne').const_mul (2*Real.pi*I)
  rw [integral_add_compl measurableSet_Icc hKI] at hsum
  apply hsum.congr'
  filter_upwards [hsmall] with y hy
  exact integral_add_compl measurableSet_Icc (pairedMomentKernel_integrable hα hα1 hy.1 hy.2)

theorem momentTransform_cauchy_upper {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hz : 0<z.im) :
    momentTransform α z=densityCauchyTransform (reciprocalMomentDensity α) z := by
  have hl := pairedMomentKernel_integral_tendsto hα hα1 hz
  have hc : Tendsto (fun y:ℝ=>∫ x:ℝ,pairedMomentKernel α y z x) (𝓝[>] (0:ℝ))
      (𝓝 ((2*Real.pi*I)*momentTransform α z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hz)] with y hy hyz
    exact (pairedMomentKernel_integral hα hα1 hy hyz).symm
  have he := tendsto_nhds_unique hc hl
  have he' : (2*Real.pi*I)*momentTransform α z=
      (2*Real.pi*I)*densityCauchyTransform (reciprocalMomentDensity α) z := by
    simpa only [densityCauchyTransform,densityCauchyKernel,mul_div_assoc,integral_const_mul] using he
  exact mul_left_cancel₀ (by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) he'

end AperyMoments
