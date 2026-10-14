import AperyMoments.LeftResolvent

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

/-- Schwarz completion of the actual reciprocal resolvent. Values on the positive cut
are immaterial; outside the cut they use the original Cauchy integral. -/
def momentTransform (α : ℝ) (s : ℂ) : ℂ :=
  if 0 < s.im then reciprocalResolvent α s
  else if s.im < 0 then starRingEnd ℂ (reciprocalResolvent α (starRingEnd ℂ s))
  else if s.re < 0 then leftResolvent α s
  else spectralCauchyTransform (2 * Real.sqrt α) (reciprocalMap α s) / Complex.sqrt s

theorem momentTransform_upper (α : ℝ) {s : ℂ} (hs : 0 < s.im) :
    momentTransform α s = reciprocalResolvent α s := by simp [momentTransform, hs]

theorem momentTransform_lower (α : ℝ) {s : ℂ} (hs : s.im < 0) :
    momentTransform α s = starRingEnd ℂ (reciprocalResolvent α (starRingEnd ℂ s)) := by
  simp [momentTransform, hs, not_lt.mpr hs.le]

theorem momentTransform_negative (α : ℝ) {x : ℝ} (hx : x < 0) :
    momentTransform α (x : ℂ) = leftResolvent α (x : ℂ) := by simp [momentTransform, hx]

theorem momentTransform_differentiableAt_nonreal {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {s : ℂ} (hs : s.im ≠ 0) : DifferentiableAt ℂ (momentTransform α) s := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · have hsc : 0 < (starRingEnd ℂ s).im := by simpa using neg_pos.mpr hs
    have hd := (reciprocalResolvent_differentiableAt hα hα1 hsc).conj_conj
    simp only [starRingEnd_apply, star_star] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Iio_mem_nhds hs)] with z hz
    exact momentTransform_lower α hz
  · apply (reciprocalResolvent_differentiableAt hα hα1 hs).congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hs)] with z hz
    exact momentTransform_upper α hz

theorem momentTransform_negative_upper_limit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : x < 0) :
    Tendsto (momentTransform α) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (momentTransform α (x : ℂ))) := by
  rw [momentTransform_negative α hx]
  apply ((leftResolvent_differentiableAt_real hα hα1 hx).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [momentTransform_upper α hz, leftResolvent_eq_upper α hz]

theorem momentTransform_negative_lower_limit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : x < 0) :
    Tendsto (momentTransform α) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (momentTransform α (x : ℂ))) := by
  have hc := (leftResolvent_differentiableAt_real hα hα1 hx).continuousAt
  have hcc : ContinuousAt (fun z : ℂ => starRingEnd ℂ (leftResolvent α (starRingEnd ℂ z))) (x : ℂ) := by
    apply (show Continuous (starRingEnd ℂ) by fun_prop).continuousAt.comp
    have hc' : ContinuousAt (leftResolvent α) (starRingEnd ℂ (x : ℂ)) := by simpa using hc
    exact hc'.comp (f := starRingEnd ℂ) (by fun_prop)
  have he : starRingEnd ℂ (leftResolvent α (x : ℂ)) = leftResolvent α (x : ℂ) := by
    apply Complex.ext <;> simp [leftResolvent_real hα hα1 hx]
  have hl := hcc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
  simp only [Complex.conj_ofReal, he] at hl
  rw [momentTransform_negative α hx]
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [momentTransform_lower α hz, leftResolvent_eq_upper α (by simpa using neg_pos.mpr hz)]

theorem momentTransform_analyticAt_negative {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {a : ℝ} (ha : a < 0) : AnalyticAt ℂ (momentTransform α) (a : ℂ) := by
  have hr : 0 < -a/2 := by linarith
  have hneg : ∀ x : ℝ, (x : ℂ) ∈ ball (a : ℂ) (-a/2) → x < 0 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hx
    linarith [hx.2]
  have hc : ContinuousOn (momentTransform α) (ball (a : ℂ) (-a/2)) := by
    apply continuousOn_of_halfPlane_limits
    · intro z _ hz
      exact (momentTransform_differentiableAt_nonreal hα hα1 hz).continuousAt
    · intro x hx
      exact momentTransform_negative_lower_limit hα hα1 (hneg x hx)
    · intro x hx
      exact momentTransform_negative_upper_limit hα hα1 (hneg x hx)
  have hd := differentiableOn_ball_of_continuousOn_off_real hc
    (fun z _ hz => momentTransform_differentiableAt_nonreal hα hα1 hz)
  exact hd.analyticOnNhd isOpen_ball _ (mem_ball_self hr)

end AperyMoments
