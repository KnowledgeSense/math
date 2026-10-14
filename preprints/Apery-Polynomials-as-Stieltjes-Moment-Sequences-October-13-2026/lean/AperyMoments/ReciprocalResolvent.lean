import AperyMoments.ContinuedCauchy
import AperyMoments.ReciprocalMap
import Mathlib.Analysis.Complex.SqrtDeriv

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def reciprocalResolvent (α : ℝ) (s : ℂ) : ℂ :=
  continuedCauchy (2 * Real.sqrt α) (reciprocalMap α s) / Complex.sqrt s

theorem reciprocalMap_differentiableAt (α : ℝ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (reciprocalMap α) s := by
  have hq := Complex.differentiableAt_sqrt hs
  have hne : Complex.sqrt s ≠ 0 := by
    unfold Complex.sqrt
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hs))
  exact hq.add ((differentiableAt_const (α : ℂ)).div hq hne)

theorem reciprocalMap_mem_continuedCauchyDomain {α : ℝ} (hα : 0 < α)
    {s : ℂ} (hs : 0 < s.im) : reciprocalMap α s ∈ continuedCauchyDomain (2 * Real.sqrt α) := by
  by_cases hi : (reciprocalMap α s).im = 0
  · have hn := (reciprocalMap_im_sign hs α).2.1.mp hi
    have hp := reciprocalMap_on_semicircle hs hα hn
    exact Or.inr (by rw [abs_of_pos hp.1]; exact hp.2.1)
  · exact Or.inl hi

theorem reciprocalResolvent_differentiableAt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ (reciprocalResolvent α) s := by
  have hb : 0 < 2 * Real.sqrt α := by positivity
  have hb2 : 2 * Real.sqrt α ≤ 2 := by
    have hh : Real.sqrt α ≤ 1 := (Real.sqrt_le_one).mpr hα1
    linarith
  have hsl : s ∈ Complex.slitPlane := Or.inr (ne_of_gt hs)
  have hc := (continuedCauchy_analyticOnNhd hb hb2 _
    (reciprocalMap_mem_continuedCauchyDomain hα hs)).differentiableAt
  apply (hc.comp s (reciprocalMap_differentiableAt α hsl)).div (Complex.differentiableAt_sqrt hsl)
  intro he
  have hp := (sqrt_upper_parts hs).1
  rw [he] at hp
  simp at hp

theorem reciprocalResolvent_analyticOnNhd {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    AnalyticOnNhd ℂ (reciprocalResolvent α) {s : ℂ | 0 < s.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro s hs
  exact (reciprocalResolvent_differentiableAt hα hα1 hs).differentiableWithinAt

theorem reciprocalResolvent_outer {α : ℝ} {s : ℂ} (hs : 0 < s.im) (hn : α < ‖s‖) :
    reciprocalResolvent α s = spectralCauchyTransform (2 * Real.sqrt α) (reciprocalMap α s) /
      Complex.sqrt s := by
  unfold reciprocalResolvent
  rw [continuedCauchy_upper _ ((reciprocalMap_im_sign hs α).2.2.mpr hn)]

theorem reciprocalResolvent_inner {α : ℝ} {s : ℂ} (hs : 0 < s.im) (hn : ‖s‖ < α) :
    reciprocalResolvent α s =
      (spectralCauchyTransform (2 * Real.sqrt α) (reciprocalMap α s) -
        2 * Real.pi * Complex.I * continuedAuxiliary (2 * Real.sqrt α) (reciprocalMap α s)) /
      Complex.sqrt s := by
  unfold reciprocalResolvent
  rw [continuedCauchy_lower _ ((reciprocalMap_im_sign hs α).1.mpr hn)]

end AperyMoments
