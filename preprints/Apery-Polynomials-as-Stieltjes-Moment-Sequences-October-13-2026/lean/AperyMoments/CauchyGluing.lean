import AperyMoments.CauchyBoundary
import AperyMoments.BoundaryExtension
import AperyMoments.HolomorphicGluing

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def cauchyLocalExtension (h : ℝ → ℝ) (F : ℂ → ℂ) (a r : ℝ) (z : ℂ) : ℂ :=
  if z.im < 0 then densityCauchyTransform h z - 2 * Real.pi * Complex.I * F z
  else if 0 < z.im then densityCauchyTransform h z
  else cauchyLocalBoundary h F a r z.re - Real.pi * Complex.I * F z

theorem cauchyLocalExtension_upper (h : ℝ → ℝ) (F : ℂ → ℂ) (a r : ℝ)
    {z : ℂ} (hz : 0 < z.im) : cauchyLocalExtension h F a r z = densityCauchyTransform h z := by
  simp [cauchyLocalExtension, hz, not_lt.mpr hz.le]

theorem cauchyLocalExtension_lower (h : ℝ → ℝ) (F : ℂ → ℂ) (a r : ℝ)
    {z : ℂ} (hz : z.im < 0) : cauchyLocalExtension h F a r z =
      densityCauchyTransform h z - 2 * Real.pi * Complex.I * F z := by
  simp [cauchyLocalExtension, hz]

theorem cauchyLocalExtension_ofReal (h : ℝ → ℝ) (F : ℂ → ℂ) (a r x : ℝ) :
    cauchyLocalExtension h F a r (x : ℂ) =
      cauchyLocalBoundary h F a r x - Real.pi * Complex.I * F (x : ℂ) := by
  simp [cauchyLocalExtension]

theorem cauchyLocalExtension_differentiableAt_nonreal {h : ℝ → ℝ}
    (hh : Measurable h) (hi : Integrable h) {F : ℂ → ℂ} {a r : ℝ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (cauchyLocalExtension h F a r) z := by
  have hg := densityCauchyTransform_differentiableAt hh hi (abs_pos.mpr hz)
    (fun t _ => cauchy_separation_nonreal hz t)
  rcases lt_or_gt_of_ne hz with hz | hz
  · apply (hg.sub (hF.const_mul (2 * Real.pi * Complex.I))).congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Iio_mem_nhds hz)] with w hw
    exact cauchyLocalExtension_lower h F a r hw
  · apply hg.congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hz)] with w hw
    exact cauchyLocalExtension_upper h F a r hw

theorem cauchyLocalExtension_continuousOn {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    (hA : AnalyticOnNhd ℂ F (ball (a : ℂ) r))
    (heq : ∀ t ∈ Icc (a - r) (a + r), (h t : ℂ) = F (t : ℂ)) :
    ContinuousOn (cauchyLocalExtension h F a r) (ball (a : ℂ) r) := by
  apply continuousOn_of_halfPlane_limits
  · intro z hz hzi
    exact (cauchyLocalExtension_differentiableAt_nonreal hh hi (hA z hz).differentiableAt hzi).continuousAt
  · intro x hx
    have hxi : x ∈ Ioo (a-r) (a+r) := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hx
      constructor <;> linarith [hx.1, hx.2]
    have hl := (densityCauchy_tendsto_lower hh hi hr hF heq hxi).sub
      (((hA (x : ℂ) hx).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))).const_mul (2 * Real.pi * Complex.I))
    have he : (fun z => densityCauchyTransform h z - 2 * Real.pi * Complex.I * F z) =ᶠ[
        𝓝[{z : ℂ | z.im < 0}] (x : ℂ)] cauchyLocalExtension h F a r := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (cauchyLocalExtension_lower h F a r hz).symm
    rw [cauchyLocalExtension_ofReal]
    convert hl.congr' he using 1
    congr 1
    ring
  · intro x hx
    have hxi : x ∈ Ioo (a-r) (a+r) := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hx
      constructor <;> linarith [hx.1, hx.2]
    rw [cauchyLocalExtension_ofReal]
    apply (densityCauchy_tendsto_upper hh hi hr hF heq hxi).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (cauchyLocalExtension_upper h F a r hz).symm

/-- The actual Cauchy transform continues through an interval where its density is analytic. -/
theorem cauchyLocalExtension_analyticOnNhd {h : ℝ → ℝ} (hh : Measurable h) (hi : Integrable h)
    {F : ℂ → ℂ} {a r : ℝ} (hr : 0 < r) {K : NNReal}
    (hF : LipschitzOnWith K F (closedBall (a : ℂ) (2 * r)))
    (hA : AnalyticOnNhd ℂ F (ball (a : ℂ) r))
    (heq : ∀ t ∈ Icc (a - r) (a + r), (h t : ℂ) = F (t : ℂ)) :
    AnalyticOnNhd ℂ (cauchyLocalExtension h F a r) (ball (a : ℂ) r) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply differentiableOn_ball_of_continuousOn_off_real
    (cauchyLocalExtension_continuousOn hh hi hr hF hA heq)
  intro z hz hzi
  exact cauchyLocalExtension_differentiableAt_nonreal hh hi (hA z hz).differentiableAt hzi

end AperyMoments
