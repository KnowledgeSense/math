import AperyMoments.ReciprocalBoundaryGeometry
import AperyMoments.CauchyVanishing
import AperyMoments.CauchyImaginaryBoundary
import AperyMoments.SpectralDensityContinuity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem sqrt_im_mul_cauchy_re_tendsto {α x : ℝ} (_hα : 0 ≤ α) (hx : 0 < x) (hne : x ≠ α) :
    Tendsto (fun s : ℂ => (Complex.sqrt s).im *
      (spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)).re)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 0) := by
  have hh := spectralDensity_measurable (2*Real.sqrt α)
  have hi := spectralDensity_integrable (show 0 ≤ 2*Real.sqrt α by positivity)
  have hv := (imaginary_mul_cauchy_tendsto_zero hh hi (reciprocalRadius α x)).comp
    (reciprocalMap_tendsto_nonreal hx hne)
  have hvr := Complex.continuous_re.continuousAt.tendsto.comp hv
  simp only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] at hvr
  have hn := (complex_norm_tendsto_positive hx).mono_left
    (nhdsWithin_le_nhds (s := {s : ℂ | 0 < s.im}))
  have hd : Tendsto (fun s : ℂ => 1-α/‖s‖) (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝 (1-α/x)) := tendsto_const_nhds.sub (tendsto_const_nhds.div hn (ne_of_gt hx))
  have hd0 : 1-α/x ≠ 0 := by
    intro he
    apply hne
    have hd' := (sub_eq_zero.mp he)
    simpa using (eq_div_iff (ne_of_gt hx)).mp hd'
  have hl := hvr.div hd hd0
  simp only [zero_div] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin, hd.eventually (eventually_ne_nhds hd0)] with s hs hds
  change ((reciprocalMap α s).im * (spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)).re) /
    (1-α/‖s‖) = _
  rw [reciprocalMap_im hs]
  field_simp

theorem outerResolvent_im_tendsto_of_cauchy {α x L : ℝ} (hα : 0 ≤ α) (hx : 0 < x) (hne : x ≠ α)
    (hg : Tendsto (fun s : ℂ => (spectralCauchyTransform (2*Real.sqrt α) (reciprocalMap α s)).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 L)) :
    Tendsto (fun s : ℂ => (outerResolvent α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (L / Real.sqrt x)) := by
  have hq : Tendsto Complex.sqrt (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ)) (𝓝 (Real.sqrt x : ℂ)) := by
    simpa only [complexSqrt_ofReal_nonneg hx.le] using
      (Complex.differentiableAt_sqrt (z := (x : ℂ)) (Or.inl hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hqr := Complex.continuous_re.continuousAt.tendsto.comp hq
  have hqn := (show Continuous Complex.normSq by fun_prop).continuousAt.tendsto.comp hq
  simp only [Complex.ofReal_re] at hqr
  have hnorm : Complex.normSq (Real.sqrt x : ℂ) = x := by simp [Complex.normSq_apply, ← pow_two, Real.sq_sqrt hx.le]
  rw [hnorm] at hqn
  have hv := sqrt_im_mul_cauchy_re_tendsto hα hx hne
  have hl := ((hg.mul hqr).sub hv).div hqn (ne_of_gt hx)
  simp only [sub_zero] at hl
  have he : (L * Real.sqrt x)/x = L/Real.sqrt x := by
    have hs := Real.sq_sqrt hx.le
    have hp := Real.sqrt_pos.mpr hx
    apply (div_eq_div_iff (ne_of_gt hx) (ne_of_gt hp)).mpr
    linear_combination L * hs
  rw [he] at hl
  convert hl using 1
  funext s
  simp only [outerResolvent, Complex.div_im, Function.comp_def, Pi.div_apply]
  ring

theorem outerResolvent_im_tendsto_outer {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (hαx : α < x) :
    Tendsto (fun s : ℂ => (outerResolvent α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝 ((-Real.pi * spectralDensity (2*Real.sqrt α) (reciprocalRadius α x))/Real.sqrt x)) := by
  apply outerResolvent_im_tendsto_of_cauchy hα.le hx (ne_of_gt hαx)
  exact (densityCauchy_im_tendsto_upper (spectralDensity_measurable _)
    (spectralDensity_integrable (by positivity))
    (spectralDensity_continuousAt_outer (by positivity) (reciprocalRadius_gt hα.le hx (ne_of_gt hαx)))).comp
      (reciprocalMap_tendsto_upper hx hαx)

theorem outerResolvent_im_tendsto_inner {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (hxα : x < α) :
    Tendsto (fun s : ℂ => (outerResolvent α s).im)
      (𝓝[{s : ℂ | 0 < s.im}] (x : ℂ))
      (𝓝 ((Real.pi * spectralDensity (2*Real.sqrt α) (reciprocalRadius α x))/Real.sqrt x)) := by
  apply outerResolvent_im_tendsto_of_cauchy hα.le hx (ne_of_lt hxα)
  exact (densityCauchy_im_tendsto_lower (spectralDensity_measurable _)
    (spectralDensity_integrable (by positivity))
    (spectralDensity_continuousAt_outer (by positivity) (reciprocalRadius_gt hα.le hx (ne_of_lt hxα)))).comp
      (reciprocalMap_tendsto_lower hx hxα)

end AperyMoments
