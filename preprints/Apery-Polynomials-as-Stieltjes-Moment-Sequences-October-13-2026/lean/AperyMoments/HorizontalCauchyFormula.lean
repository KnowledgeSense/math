import AperyMoments.HorizontalCauchyHeight

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

theorem horizontal_difference_of_decay (F : ℂ→ℂ) (z : ℂ) (C R c d : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcd : c≤d)
    (hcz : c≠z.im) (hdz : d≠z.im)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    (∫ x:ℝ,horizontalKernel F z c x)-(∫ x:ℝ,horizontalKernel F z d x)=
      F z*(inverseLineLimit (c-z.im)-inverseLineLimit (d-z.im)) := by
  have hv := vertical_bounded_of_decay F z C R c d hC hc hcd hF
  exact horizontal_difference_of_vertical_limits F z c d hhol hc hcd hcz hdz
    (horizontalKernel_integrable F z C R c hC hR hc hcz hhol hF)
    (horizontalKernel_integrable F z C R d hC hR (hc.trans_le hcd) hdz hhol hF)
    (vertical_dslope_limit_right_of_bounded F z C c d hv.1)
    (vertical_dslope_limit_left_of_bounded F z C c d hv.2)

theorem horizontal_integral_eq (F : ℂ→ℂ) (z : ℂ) (C R c : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcz : c≠z.im)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    (∫ x:ℝ,horizontalKernel F z c x)=F z*(inverseLineLimit (c-z.im)+Real.pi*I) := by
  have hh := horizontal_integral_tendsto_height F z C R hC hR hhol hF
  have he : (fun d:ℝ => (∫ x:ℝ,horizontalKernel F z c x)-(∫ x:ℝ,horizontalKernel F z d x))
      =ᶠ[atTop] (fun _ => F z*(inverseLineLimit (c-z.im)+Real.pi*I)) := by
    filter_upwards [eventually_ge_atTop c,eventually_gt_atTop z.im] with d hcd hdz
    rw [horizontal_difference_of_decay F z C R c d hC hR hc hcd hcz (ne_of_gt hdz) hhol hF]
    simp only [inverseLineLimit,ite_eq_left (sub_pos.mpr hdz),neg_mul,sub_neg_eq_add]
  have ht := tendsto_const_nhds.congr' he.symm
  have hu := tendsto_nhds_unique (hh.const_sub (∫ x:ℝ,horizontalKernel F z c x)) ht
  simpa only [sub_zero] using hu

theorem horizontal_integral_unshift (F : ℂ→ℂ) (z : ℂ) (c : ℝ) :
    (∫ x:ℝ,horizontalKernel F z c x)=
      ∫ x:ℝ,F ((x:ℂ)+c*I)/((x:ℂ)+c*I-z) := by
  have h := integral_add_left_eq_self (μ := volume) (fun x:ℝ => F ((x:ℂ)+c*I)/((x:ℂ)+c*I-z)) z.re
  simpa only [horizontalKernel,horizontalPoint,Complex.ofReal_add] using h

/-- Cauchy's formula on a horizontal line above the real axis. -/
theorem horizontal_cauchy_formula (F : ℂ→ℂ) (z : ℂ) (C R c : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcz : c<z.im)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    (∫ x:ℝ,F ((x:ℂ)+c*I)/((x:ℂ)+c*I-z))=(2*Real.pi*I)*F z := by
  rw [← horizontal_integral_unshift,horizontal_integral_eq F z C R c hC hR hc (ne_of_lt hcz) hhol hF]
  rw [inverseLineLimit,ite_eq_right (by linarith : ¬0<c-z.im)]
  ring

/-- The same integral vanishes when the evaluation point is below the line. -/
theorem horizontal_cauchy_formula_below (F : ℂ→ℂ) (z : ℂ) (C R c : ℝ)
    (hC : 0≤C) (hR : 0≤R) (hc : 0<c) (hcz : z.im<c)
    (hhol : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v)
    (hF : ∀w:ℂ,0<w.im→R≤‖w‖→‖F w‖≤C/‖w‖) :
    (∫ x:ℝ,F ((x:ℂ)+c*I)/((x:ℂ)+c*I-z))=0 := by
  rw [← horizontal_integral_unshift,horizontal_integral_eq F z C R c hC hR hc (ne_of_gt hcz) hhol hF]
  rw [inverseLineLimit,ite_eq_left (sub_pos.mpr hcz)]
  ring

end AperyMoments
