import AperyMoments.HorizontalCauchyKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology Interval

theorem upper_dslope_continuousAt (F : ℂ→ℂ) (z w : ℂ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hw : 0<w.im) :
    ContinuousAt (dslope F z) w := by
  by_cases he : w=z
  · subst w
    exact continuousAt_dslope_same.mpr (hF z hw)
  · exact (continuousAt_dslope_of_ne he).mpr (hF w hw).continuousAt

theorem upper_dslope_rectangle_zero (F : ℂ→ℂ) (z : ℂ) (a b c d : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcd : c≤d) :
    rectangleBoundary (dslope F z) a b c d=0 := by
  have hpos : ∀w∈([[a,b]] ×ℂ [[c,d]]),0<w.im := by
    intro w hw
    have ht : c≤w.im := by simpa only [min_eq_left hcd] using hw.2.1
    exact hc.trans_le ht
  have hcont : ContinuousOn (dslope F z) ([[a,b]] ×ℂ [[c,d]]) := by
    intro w hw
    exact (upper_dslope_continuousAt F z w hF (hpos w hw)).continuousWithinAt
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (dslope F z) (⟨a,c⟩:ℂ) (⟨b,d⟩:ℂ) {z} (countable_singleton z) hcont
  intro w hw
  apply (differentiableAt_dslope_of_ne (show w≠z by simpa using hw.2)).mpr
  apply hF w
  have hc' : min c d=c := min_eq_left hcd
  have ht : c<w.im := by simpa only [hc'] using hw.1.2.1
  exact hc.trans ht

end AperyMoments
