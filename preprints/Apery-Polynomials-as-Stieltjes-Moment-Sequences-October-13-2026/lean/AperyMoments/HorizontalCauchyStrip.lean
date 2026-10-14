import AperyMoments.HorizontalCauchyLine

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def inverseLineLimit (c : ℝ) : ℂ := if 0<c then -Real.pi*I else Real.pi*I

theorem horizontal_inverse_limit {c : ℝ} (hc : c≠0) :
    Tendsto (fun r:ℝ => ∫ x:ℝ in -r..r,((x:ℂ)+c*I)⁻¹) atTop (𝓝 (inverseLineLimit c)) := by
  by_cases hp : 0<c
  · simpa [inverseLineLimit,hp] using horizontal_inverse_limit_positive hp
  · simpa [inverseLineLimit,hp] using horizontal_inverse_limit_negative (show c<0 by rcases lt_or_gt_of_ne hc with h|h; exact h; exact False.elim (hp h))

theorem horizontal_integral_shift (G : ℂ→ℂ) (z : ℂ) (c r : ℝ) :
    (∫ x:ℝ in -r..r,G (horizontalPoint z c x))=
      ∫ x:ℝ in z.re-r..z.re+r,G ((x:ℂ)+c*I) := by
  have h := intervalIntegral.integral_comp_add_left (f := fun x:ℝ => G ((x:ℂ)+c*I))
    (a := -r) (b := r) z.re
  simpa only [horizontalPoint,Complex.ofReal_add,sub_eq_add_neg] using h

theorem centered_dslope_boundary (F : ℂ→ℂ) (z : ℂ) (c d r : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcd : c≤d) :
    (∫ x:ℝ in -r..r,dslope F z (horizontalPoint z c x))-
    (∫ x:ℝ in -r..r,dslope F z (horizontalPoint z d x))+
      I*(∫ y:ℝ in c..d,dslope F z ((z.re+r:ℝ)+y*I))-
      I*(∫ y:ℝ in c..d,dslope F z ((z.re-r:ℝ)+y*I))=0 := by
  rw [horizontal_integral_shift,horizontal_integral_shift]
  exact upper_dslope_rectangle_zero F z (z.re-r) (z.re+r) c d hF hc hcd

theorem dslope_horizontal_limit (F : ℂ→ℂ) (z : ℂ) (c : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcz : c≠z.im)
    (hI : Integrable (horizontalKernel F z c)) :
    Tendsto (fun r:ℝ => ∫ x:ℝ in -r..r,dslope F z (horizontalPoint z c x)) atTop
      (𝓝 ((∫ x:ℝ,horizontalKernel F z c x)-F z*inverseLineLimit (c-z.im))) := by
  have h1 := intervalIntegral_tendsto_integral hI tendsto_neg_atTop_atBot tendsto_id
  have h2 := horizontal_inverse_limit (sub_ne_zero.mpr hcz)
  have h := h1.sub (h2.const_mul (F z))
  have he (r:ℝ) :
      (∫ x:ℝ in -r..r,dslope F z (horizontalPoint z c x))=
      (∫ x:ℝ in -r..r,horizontalKernel F z c x)-F z*(∫ x:ℝ in -r..r,((x:ℂ)+(c-z.im:ℝ)*I)⁻¹) := by
    simpa only [Complex.ofReal_sub] using dslope_horizontal_integral F z c (-r) r hF hc hcz
  exact h.congr (fun r => (he r).symm)

theorem horizontal_difference_of_vertical_limits (F : ℂ→ℂ) (z : ℂ) (c d : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcd : c≤d)
    (hcz : c≠z.im) (hdz : d≠z.im)
    (hIc : Integrable (horizontalKernel F z c)) (hId : Integrable (horizontalKernel F z d))
    (hR : Tendsto (fun r:ℝ => ∫ y:ℝ in c..d,dslope F z ((z.re+r:ℝ)+y*I)) atTop (𝓝 0))
    (hL : Tendsto (fun r:ℝ => ∫ y:ℝ in c..d,dslope F z ((z.re-r:ℝ)+y*I)) atTop (𝓝 0)) :
    (∫ x:ℝ,horizontalKernel F z c x)-(∫ x:ℝ,horizontalKernel F z d x)=
      F z*(inverseLineLimit (c-z.im)-inverseLineLimit (d-z.im)) := by
  have h1 := dslope_horizontal_limit F z c hF hc hcz hIc
  have h2 := dslope_horizontal_limit F z d hF (hc.trans_le hcd) hdz hId
  have h := ((h1.sub h2).add (hR.const_mul I)).sub (hL.const_mul I)
  have he : Tendsto (fun r:ℝ =>
      (∫ x:ℝ in -r..r,dslope F z (horizontalPoint z c x))-
      (∫ x:ℝ in -r..r,dslope F z (horizontalPoint z d x))+
        I*(∫ y:ℝ in c..d,dslope F z ((z.re+r:ℝ)+y*I))-
        I*(∫ y:ℝ in c..d,dslope F z ((z.re-r:ℝ)+y*I))) atTop (𝓝 0) := by
    simpa only [centered_dslope_boundary F z c d _ hF hc hcd] using
      (tendsto_const_nhds : Tendsto (fun _:ℝ => (0:ℂ)) atTop (𝓝 0))
  have hh := tendsto_nhds_unique h he
  simp only [mul_zero,add_zero,sub_zero] at hh
  linear_combination hh

end AperyMoments
