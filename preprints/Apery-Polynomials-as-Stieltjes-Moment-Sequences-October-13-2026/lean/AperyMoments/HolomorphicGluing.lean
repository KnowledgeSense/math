import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

noncomputable section
open Complex MeasureTheory Metric Set
open scoped Topology Interval
namespace AperyMoments

def rectangleBoundary (F : ℂ→ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x:ℝ in a..b,F (x+c*I))-(∫ x:ℝ in a..b,F (x+d*I))+
    I*(∫ y:ℝ in c..d,F (b+y*I))-I*(∫ y:ℝ in c..d,F (a+y*I))

theorem rectangleBoundary_zero_one_side (F : ℂ→ℂ) (a b c d : ℝ)
    (hc : ContinuousOn F ([[a,b]] ×ℂ [[c,d]]))
    (hd : ∀z∈([[a,b]] ×ℂ [[c,d]]),z.im≠0 → DifferentiableAt ℂ F z)
    (hs : ∀y∈Ioo (min c d) (max c d),y≠0) :
    rectangleBoundary F a b c d=0 := by
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F
    (⟨a,c⟩:ℂ) (⟨b,d⟩:ℂ) hc
  intro z hz
  apply (hd z ?_ (hs z.im hz.2)).differentiableWithinAt
  exact ⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩

theorem zero_not_between_endpoint (a : ℝ) :
    ∀y∈Ioo (min a 0) (max a 0),y≠0 := by
  intro y hy he
  subst y
  rcases le_total a 0 with h | h
  · rw [max_eq_right h] at hy
    exact (lt_irrefl 0) hy.2
  · rw [min_eq_right h] at hy
    exact (lt_irrefl 0) hy.1

theorem vertical_interval_integrable (F : ℂ→ℂ) (a b c d x : ℝ)
    (hc : ContinuousOn F ([[a,b]] ×ℂ [[c,d]])) (hx : x∈[[a,b]]) :
    IntervalIntegrable (fun y:ℝ => F (x+y*I)) volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp (by fun_prop)
  intro y hy
  simpa using (show (x+y*I:ℂ)∈([[a,b]] ×ℂ [[c,d]]) from by
    simpa [mem_reProdIm] using And.intro hx hy)

theorem rectangleBoundary_zero_off_axis (F : ℂ→ℂ) (a b c d : ℝ)
    (hc : ContinuousOn F ([[a,b]] ×ℂ [[c,d]]))
    (hd : ∀z∈([[a,b]] ×ℂ [[c,d]]),z.im≠0 → DifferentiableAt ℂ F z) :
    rectangleBoundary F a b c d=0 := by
  by_cases hz : (0:ℝ)∈[[c,d]]
  · have hleft : ([[a,b]] ×ℂ [[c,0]]) ⊆ ([[a,b]] ×ℂ [[c,d]]) := by
      intro z hz'
      exact ⟨hz'.1,uIcc_subset_uIcc_left hz hz'.2⟩
    have hright : ([[a,b]] ×ℂ [[0,d]]) ⊆ ([[a,b]] ×ℂ [[c,d]]) := by
      intro z hz'
      exact ⟨hz'.1,uIcc_subset_uIcc_right hz hz'.2⟩
    have hcL := hc.mono hleft
    have hcR := hc.mono hright
    have hl := rectangleBoundary_zero_one_side F a b c 0 hcL
      (fun z hz' => hd z (hleft hz')) (zero_not_between_endpoint c)
    have hr := rectangleBoundary_zero_one_side F a b 0 d hcR
      (fun z hz' => hd z (hright hz')) (by simpa only [min_comm,max_comm] using zero_not_between_endpoint d)
    have haL := vertical_interval_integrable F a b c 0 a hcL left_mem_uIcc
    have haR := vertical_interval_integrable F a b 0 d a hcR left_mem_uIcc
    have hbL := vertical_interval_integrable F a b c 0 b hcL right_mem_uIcc
    have hbR := vertical_interval_integrable F a b 0 d b hcR right_mem_uIcc
    have ha := intervalIntegral.integral_add_adjacent_intervals haL haR
    have hb := intervalIntegral.integral_add_adjacent_intervals hbL hbR
    unfold rectangleBoundary at *
    rw [← ha,← hb]
    linear_combination hl+hr
  · apply rectangleBoundary_zero_one_side F a b c d hc hd
    intro y hy he
    subst y
    exact hz ⟨hy.1.le,hy.2.le⟩

/-- A continuous function holomorphic off the real axis is holomorphic across it. -/
theorem differentiableOn_ball_of_continuousOn_off_real {F : ℂ→ℂ} {c : ℂ} {r : ℝ}
    (hcont : ContinuousOn F (ball c r))
    (hd : ∀z∈ball c r,z.im≠0 → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F (ball c r) := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).mp
  refine ⟨?_,hcont⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
  exact rectangleBoundary_zero_off_axis F z.re w.re z.im w.im
    (hcont.mono hrect) (fun x hx => hd x (hrect hx))

end AperyMoments
