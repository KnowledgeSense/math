import AperyMoments.MomentReconstruction
import AperyMoments.ReciprocalTransformSeries

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem reciprocalMomentCauchy_differentiableAt {α R : ℝ}
    (hα : 0<α) (hα1 : α≤1) (hR : 64<R) :
    DifferentiableAt ℂ (densityCauchyTransform (reciprocalMomentDensity α)) (R:ℂ) := by
  apply densityCauchyTransform_differentiableAt (reciprocalMomentDensity_measurable α)
    (reciprocalMomentDensity_integrable hα hα1) (sub_pos.mpr hR)
  intro t ht
  have hs : t∈Icc 0 64 := by
    by_contra hn
    exact ht (reciprocalMomentDensity_support hα hα1 hn)
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hs.2] : 0<R-t)]
  linarith [hs.2]

theorem momentTransform_cauchy_real {α R : ℝ}
    (hα : 0<α) (hα1 : α≤1) (hR : 64<R) :
    momentTransform α (R:ℂ)=densityCauchyTransform (reciprocalMomentDensity α) (R:ℂ) := by
  have hc : Tendsto (fun y:ℝ=>(y:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun y:ℝ=>(R:ℂ)+y*I) (𝓝[>] (0:ℝ)) (𝓝 (R:ℂ)) := by
    simpa only [zero_mul,add_zero] using (hc.mul_const I).const_add (R:ℂ)
  have hM := (momentTransform_analyticAt_large hα hα1 hR).continuousAt.tendsto.comp hp
  have hG := (reciprocalMomentCauchy_differentiableAt hα hα1 hR).continuousAt.tendsto.comp hp
  have he : (fun y:ℝ=>momentTransform α ((R:ℂ)+y*I)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y=>densityCauchyTransform (reciprocalMomentDensity α) ((R:ℂ)+y*I)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact momentTransform_cauchy_upper hα hα1 (by simpa using hy)
  exact tendsto_nhds_unique (hM.congr' he) hG

theorem reciprocalMomentCauchy_hasSum {α R : ℝ}
    (hα : 0<α) (hα1 : α≤1) (hR : 256<R) :
    HasSum (fun n=>(reciprocalPolynomial n α:ℂ)/(R:ℂ)^(n+1))
      (densityCauchyTransform (reciprocalMomentDensity α) (R:ℂ)) := by
  have hs := reciprocal_transform_hasSum hα hα1 hR
  rw [← momentTransform_positive α (by linarith : 0≤R),
    momentTransform_cauchy_real hα hα1 (by linarith : 64<R)] at hs
  exact hs

end AperyMoments
