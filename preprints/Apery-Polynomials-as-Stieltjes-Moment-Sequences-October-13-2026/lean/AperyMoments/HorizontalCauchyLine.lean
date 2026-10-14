import AperyMoments.HorizontalCauchyRectangle

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def horizontalPoint (z : ℂ) (c x : ℝ) : ℂ := z.re+x+c*I

def horizontalKernel (F : ℂ→ℂ) (z : ℂ) (c x : ℝ) : ℂ :=
  F (horizontalPoint z c x)/(horizontalPoint z c x-z)

theorem horizontalPoint_sub (z : ℂ) (c x : ℝ) :
    horizontalPoint z c x-z=(x:ℂ)+(c-z.im)*I := by
  apply Complex.ext <;> simp [horizontalPoint]

theorem horizontalPoint_ne (z : ℂ) {c : ℝ} (hc : c≠z.im) (x : ℝ) :
    horizontalPoint z c x≠z := by
  intro he
  have hi := congrArg Complex.im he
  simp only [horizontalPoint,add_im,mul_im,ofReal_re,ofReal_im,I_im,I_re,
    zero_add,mul_one,mul_zero,add_zero] at hi
  exact hc hi

theorem horizontalKernel_continuous (F : ℂ→ℂ) (z : ℂ) (c : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcz : c≠z.im) :
    Continuous (horizontalKernel F z c) := by
  have hp : Continuous (horizontalPoint z c) := by unfold horizontalPoint; fun_prop
  have hfc : Continuous (fun x => F (horizontalPoint z c x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hF _ (by simpa [horizontalPoint] using hc)).continuousAt.comp hp.continuousAt
  exact hfc.div (hp.sub continuous_const) (fun x => sub_ne_zero.mpr (horizontalPoint_ne z hcz x))

theorem dslope_horizontal_eq (F : ℂ→ℂ) (z : ℂ) (c x : ℝ) (hc : c≠z.im) :
    dslope F z (horizontalPoint z c x)=
      horizontalKernel F z c x-F z*((x:ℂ)+(c-z.im)*I)⁻¹ := by
  rw [dslope_of_ne F (horizontalPoint_ne z hc x),slope_def_module,smul_eq_mul]
  rw [horizontalKernel,horizontalPoint_sub]
  ring

theorem dslope_horizontal_integral (F : ℂ→ℂ) (z : ℂ) (c a b : ℝ)
    (hF : ∀v:ℂ,0<v.im→DifferentiableAt ℂ F v) (hc : 0<c) (hcz : c≠z.im) :
    (∫ x:ℝ in a..b,dslope F z (horizontalPoint z c x))=
      (∫ x:ℝ in a..b,horizontalKernel F z c x)-
        F z*(∫ x:ℝ in a..b,((x:ℂ)+(c-z.im)*I)⁻¹) := by
  have hi : Continuous (fun x:ℝ => ((x:ℂ)+(c-z.im)*I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x he
    have hh := congrArg Complex.im he
    simp at hh
    exact hcz (by linarith)
  have hfi : IntervalIntegrable (fun x:ℝ => F z*((x:ℂ)+(c-z.im)*I)⁻¹) volume a b :=
    (continuous_const.mul hi).intervalIntegrable a b
  simp_rw [dslope_horizontal_eq F z c _ hcz]
  rw [intervalIntegral.integral_sub
    ((horizontalKernel_continuous F z c hF hc hcz).intervalIntegrable a b)
    hfi,intervalIntegral.integral_const_mul]

end AperyMoments
