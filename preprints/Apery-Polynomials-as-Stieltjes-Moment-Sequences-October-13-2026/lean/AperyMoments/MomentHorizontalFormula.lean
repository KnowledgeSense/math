import AperyMoments.HorizontalCauchyFormula
import AperyMoments.ResolventInfinityBound

noncomputable section
open MeasureTheory
namespace AperyMoments

theorem momentTransform_horizontal_integrable {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcz : c ≠ z.im) :
    Integrable (fun x : ℝ => momentTransform α ((x : ℂ)+c*Complex.I)/((x : ℂ)+c*Complex.I-z)) := by
  have hi := horizontalKernel_integrable (momentTransform α) z 2 256 c
    (by norm_num) (by norm_num) hc hcz
    (fun _ hv => momentTransform_differentiableAt_nonreal hα hα1 hv.ne')
    (fun _ hv hn => momentTransform_infinity_bound hα hα1 hv hn)
  have ht := (measurePreserving_sub_right volume z.re).integrable_comp_of_integrable hi
  simpa only [horizontalKernel, horizontalPoint, Function.comp_def, Complex.ofReal_sub,
    add_sub_cancel] using ht

theorem momentTransform_horizontal_formula {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcz : c < z.im) :
    (∫ x : ℝ, momentTransform α ((x : ℂ)+c*Complex.I)/((x : ℂ)+c*Complex.I-z)) =
      (2*Real.pi*Complex.I)*momentTransform α z :=
  horizontal_cauchy_formula (momentTransform α) z 2 256 c
    (by norm_num) (by norm_num) hc hcz
    (fun _ hv => momentTransform_differentiableAt_nonreal hα hα1 hv.ne')
    (fun _ hv hn => momentTransform_infinity_bound hα hα1 hv hn)

theorem momentTransform_horizontal_formula_below {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcz : z.im < c) :
    (∫ x : ℝ, momentTransform α ((x : ℂ)+c*Complex.I)/((x : ℂ)+c*Complex.I-z)) = 0 :=
  horizontal_cauchy_formula_below (momentTransform α) z 2 256 c
    (by norm_num) (by norm_num) hc hcz
    (fun _ hv => momentTransform_differentiableAt_nonreal hα hα1 hv.ne')
    (fun _ hv hn => momentTransform_infinity_bound hα hα1 hv hn)

def pairedMomentKernel (α c : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  momentTransform α ((x : ℂ)+c*Complex.I)/((x : ℂ)+c*Complex.I-z) -
    starRingEnd ℂ (momentTransform α ((x : ℂ)+c*Complex.I))/((x : ℂ)-c*Complex.I-z)

theorem momentTransform_horizontal_conjugate {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hz : 0 < z.im) :
    (∫ x : ℝ, starRingEnd ℂ (momentTransform α ((x : ℂ)+c*Complex.I))/
      ((x : ℂ)-c*Complex.I-z)) = 0 := by
  have he := momentTransform_horizontal_formula_below (z := starRingEnd ℂ z) hα hα1 hc
    (by simp; linarith)
  have hh := congrArg (starRingEnd ℂ) he
  rw [← integral_conj] at hh
  simpa only [map_div₀, map_sub, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
    mul_neg, ← sub_eq_add_neg, starRingEnd_self_apply, map_zero] using hh

theorem momentTransform_horizontal_conjugate_integrable {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hz : 0 < z.im) :
    Integrable (fun x : ℝ => starRingEnd ℂ (momentTransform α ((x : ℂ)+c*Complex.I))/
      ((x : ℂ)-c*Complex.I-z)) := by
  have hi := momentTransform_horizontal_integrable (z := starRingEnd ℂ z) hα hα1 hc
    (by simp; linarith)
  have hh : Integrable (fun x : ℝ => starRingEnd ℂ
      (momentTransform α ((x : ℂ)+c*Complex.I)/((x : ℂ)+c*Complex.I-starRingEnd ℂ z))) := by
    apply hi.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hi.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => le_of_eq (Complex.norm_conj _))
  simpa only [map_div₀, map_sub, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
    mul_neg, ← sub_eq_add_neg, starRingEnd_self_apply] using hh

theorem pairedMomentKernel_integrable {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcz : c < z.im) :
    Integrable (pairedMomentKernel α c z) :=
  (momentTransform_horizontal_integrable hα hα1 hc hcz.ne).sub
    (momentTransform_horizontal_conjugate_integrable hα hα1 hc (hc.trans hcz))

theorem pairedMomentKernel_integral {α c : ℝ} {z : ℂ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hcz : c < z.im) :
    (∫ x : ℝ, pairedMomentKernel α c z x) = (2*Real.pi*Complex.I)*momentTransform α z := by
  unfold pairedMomentKernel
  rw [integral_sub (momentTransform_horizontal_integrable hα hα1 hc hcz.ne)
    (momentTransform_horizontal_conjugate_integrable hα hα1 hc (hc.trans hcz)),
    momentTransform_horizontal_formula hα hα1 hc hcz,
    momentTransform_horizontal_conjugate hα hα1 hc (hc.trans hcz), sub_zero]

end AperyMoments
