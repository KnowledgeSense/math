import AperyMoments.MomentJumpDensity
import AperyMoments.ReciprocalHorizontalGeometry

noncomputable section
namespace AperyMoments
open Complex Set Filter
open scoped Topology

theorem outerResolvent_imaginary_mul_tendsto_zero {α x : ℝ} (_hα : 0≤α)
    (hx : 0<x) (hne : x≠α) :
    Tendsto (fun s:ℂ=>(s.im:ℂ)*outerResolvent α s)
      (𝓝[{s:ℂ | 0<s.im}] (x:ℂ)) (𝓝 0) := by
  have hv := (imaginary_mul_cauchy_tendsto_zero
    (spectralDensity_measurable (2*Real.sqrt α))
    (spectralDensity_integrable (by positivity)) (reciprocalRadius α x)).comp
      (reciprocalMap_tendsto_nonreal hx hne)
  have hq : Tendsto Complex.sqrt (𝓝[{s:ℂ | 0<s.im}] (x:ℂ))
      (𝓝 (Real.sqrt x:ℂ)) := by
    simpa only [complexSqrt_ofReal_nonneg hx.le] using
      (Complex.differentiableAt_sqrt (z := (x:ℂ)) (Or.inl hx)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hqr := Complex.continuous_re.continuousAt.tendsto.comp hq
  have hn := (complex_norm_tendsto_positive hx).mono_left
    (nhdsWithin_le_nhds (s := {s:ℂ | 0<s.im}))
  have hd : Tendsto (fun s:ℂ=>1-α/‖s‖) (𝓝[{s:ℂ | 0<s.im}] (x:ℂ))
      (𝓝 (1-α/x)) := tendsto_const_nhds.sub (tendsto_const_nhds.div hn (ne_of_gt hx))
  have hd0 : 1-α/x≠0 := by
    intro he
    apply hne
    have hh := (eq_div_iff (ne_of_gt hx)).mp (sub_eq_zero.mp he)
    linarith
  have hdc : Tendsto (fun s:ℂ=>((1-α/‖s‖:ℝ):ℂ))
      (𝓝[{s:ℂ | 0<s.im}] (x:ℂ)) (𝓝 ((1-α/x:ℝ):ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have hqrc := Complex.continuous_ofReal.continuousAt.tendsto.comp hqr
  have hl := (((hqrc.const_mul 2).div hdc (Complex.ofReal_ne_zero.mpr hd0)).mul hv).div hq
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx)))
  simp only [mul_zero,zero_div] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,hd.eventually (eventually_ne_nhds hd0)] with s hs hds
  change (2*((Complex.sqrt s).re:ℂ)/((1-α/‖s‖:ℝ):ℂ)*
      (((reciprocalMap α s).im:ℂ)*spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)))/
      Complex.sqrt s=(s.im:ℂ)*outerResolvent α s
  rw [reciprocalMap_im hs]
  have hp := sqrt_upper_product hs
  have hpc : (2:ℂ)*((Complex.sqrt s).re:ℂ)*((Complex.sqrt s).im:ℂ)=(s.im:ℂ) := by exact_mod_cast hp
  unfold outerResolvent
  rw [Complex.ofReal_mul]
  have hdC : ((1-α/‖s‖:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hds
  calc
    _ = ((2*((Complex.sqrt s).re:ℂ)*((Complex.sqrt s).im:ℂ))*
        spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)/Complex.sqrt s)*
        (((1-α/‖s‖:ℝ):ℂ)/((1-α/‖s‖:ℝ):ℂ)) := by ring
    _ = _ := by rw [div_self hdC,mul_one,hpc]; ring


theorem momentTransform_imaginary_mul_tendsto_zero {α x : ℝ} (hα : 0<α)
    (hx : 0<x) (hne : x≠α) (hcut : reciprocalRadius α x≠2*Real.sqrt α+4) :
    Tendsto (fun s:ℂ=>(s.im:ℂ)*momentTransform α s)
      (𝓝[{s:ℂ | 0<s.im}] (x:ℂ)) (𝓝 0) := by
  have ho := outerResolvent_imaginary_mul_tendsto_zero hα.le hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hw := reciprocalRadius_gt hα.le hx hne
    have hH := (continuedAuxiliary_right_boundary (by positivity : 0<2*Real.sqrt α) hw hcut).comp
      (reciprocalMap_tendsto_lower hx hlt)
    have hq : Tendsto Complex.sqrt (𝓝[{s:ℂ | 0<s.im}] (x:ℂ))
        (𝓝 (Real.sqrt x:ℂ)) := by
      simpa only [complexSqrt_ofReal_nonneg hx.le] using
        (Complex.differentiableAt_sqrt (z := (x:ℂ)) (Or.inl hx)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
    have hi : Tendsto (fun s:ℂ=>(s.im:ℂ)) (𝓝[{s:ℂ | 0<s.im}] (x:ℂ)) (𝓝 0) := by
      have hi := (Complex.continuous_ofReal.comp Complex.continuous_im).tendsto (x:ℂ)
      have hi' := hi.mono_left (nhdsWithin_le_nhds (s := {s:ℂ | 0<s.im}))
      change Tendsto (fun s:ℂ=>(s.im:ℂ)) _ (𝓝 (0:ℂ)) at hi'
      exact hi'

    have hc := hi.mul ((hH.const_mul (2*Real.pi*I)).div hq
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx))))
    simp only [zero_mul] at hc
    have hl := ho.sub hc
    simp only [sub_zero] at hl
    apply hl.congr'
    have hn := (complex_norm_tendsto_positive hx).eventually (Iio_mem_nhds hlt)
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hn] with s hs hsn
    rw [momentTransform_upper α hs,reciprocalResolvent_inner hs hsn]
    simp only [outerResolvent,sub_div,mul_sub,Function.comp_def,Pi.div_apply]
  · apply ho.congr'
    have hn := (complex_norm_tendsto_positive hx).eventually (Ioi_mem_nhds hgt)
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hn] with s hs hsn
    rw [momentTransform_outer_upper α hs hsn]

end AperyMoments
