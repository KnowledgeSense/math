import AperyMoments.OuterResolvent

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

theorem momentTransform_large_upper_limit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : 64 < x) :
    Tendsto (momentTransform α) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (momentTransform α (x : ℂ))) := by
  have hxp : 0 < x := by linarith
  have hnx : α < ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]; linarith
  have hn : ∀ᶠ z : ℂ in 𝓝 (x : ℂ), α < ‖z‖ := continuous_norm.continuousAt.eventually (Ioi_mem_nhds hnx)
  rw [momentTransform_positive α hxp.le]
  apply ((outerResolvent_differentiableAt_real hα hα1 hx).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with z hz hzn
  exact (momentTransform_outer_upper α hz hzn).symm

theorem momentTransform_large_lower_limit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : 64 < x) :
    Tendsto (momentTransform α) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (momentTransform α (x : ℂ))) := by
  have hxp : 0 < x := by linarith
  have hnx : α < ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp]; linarith
  have hn : ∀ᶠ z : ℂ in 𝓝 (x : ℂ), α < ‖z‖ := continuous_norm.continuousAt.eventually (Ioi_mem_nhds hnx)
  have hc := (outerResolvent_differentiableAt_real hα hα1 hx).continuousAt
  have hcc : ContinuousAt (fun z : ℂ => starRingEnd ℂ (outerResolvent α (starRingEnd ℂ z))) (x : ℂ) := by
    apply (show Continuous (starRingEnd ℂ) by fun_prop).continuousAt.comp
    have hc' : ContinuousAt (outerResolvent α) (starRingEnd ℂ (x : ℂ)) := by simpa using hc
    exact hc'.comp (f := starRingEnd ℂ) (by fun_prop)
  have he : starRingEnd ℂ (outerResolvent α (x : ℂ)) = outerResolvent α (x : ℂ) := by
    apply Complex.ext <;> simp [outerResolvent_real α hxp.le]
  have hl := hcc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  simp only [Complex.conj_ofReal, he] at hl
  rw [momentTransform_positive α hxp.le]
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with z hz hzn
  exact (momentTransform_outer_lower α hz hzn).symm

theorem momentTransform_analyticAt_large {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {a : ℝ} (ha : 64 < a) : AnalyticAt ℂ (momentTransform α) (a : ℂ) := by
  have hr : 0 < (a-64)/2 := by linarith
  have hlarge : ∀ x : ℝ, (x : ℂ) ∈ ball (a : ℂ) ((a-64)/2) → 64 < x := by
    intro x hx
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hx
    linarith [hx.1]
  have hc : ContinuousOn (momentTransform α) (ball (a : ℂ) ((a-64)/2)) := by
    apply continuousOn_of_halfPlane_limits
    · intro z _ hz
      exact (momentTransform_differentiableAt_nonreal hα hα1 hz).continuousAt
    · intro x hx
      exact momentTransform_large_lower_limit hα hα1 (hlarge x hx)
    · intro x hx
      exact momentTransform_large_upper_limit hα hα1 (hlarge x hx)
  have hd := differentiableOn_ball_of_continuousOn_off_real hc
    (fun z _ hz => momentTransform_differentiableAt_nonreal hα hα1 hz)
  exact hd.analyticOnNhd isOpen_ball _ (mem_ball_self hr)

def momentTransformDomain : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 0 ∨ 64 < z.re}

theorem momentTransformDomain_isOpen : IsOpen momentTransformDomain :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    ((isOpen_lt Complex.continuous_re continuous_const).union (isOpen_lt continuous_const Complex.continuous_re))

/-- The actual continued transform is holomorphic off one compact nonnegative interval. -/
theorem momentTransform_analyticOnNhd {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    AnalyticOnNhd ℂ (momentTransform α) momentTransformDomain := by
  apply DifferentiableOn.analyticOnNhd _ momentTransformDomain_isOpen
  intro z hz
  by_cases hi : z.im = 0
  · have hre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    rcases hz.resolve_left (not_not.mpr hi) with hn | hp
    · have hA := momentTransform_analyticAt_negative hα hα1 hn
      simpa only [hre] using hA.differentiableAt.differentiableWithinAt
    · have hA := momentTransform_analyticAt_large hα hα1 hp
      simpa only [hre] using hA.differentiableAt.differentiableWithinAt
  · exact (momentTransform_differentiableAt_nonreal hα hα1 hi).differentiableWithinAt

end AperyMoments
